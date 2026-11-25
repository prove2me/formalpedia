-- Prove2me | solution 1 for DeMorganApprox.Main.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:19:30.735485+00:00
-- url     : https://prove2.me/submissions/95817309-cfd2-4caf-965c-8f2a5def4dc7

import Theorems.Thm_DeMorganApprox_Main_lemma_5_5

open DeMorganApprox.Main DeMorganApprox.Main.SpanProgram

namespace HelperProof

variable {m : ℕ} {I J I₁ I₂ J₁ J₂ : Type}
variable [Fintype I] [Fintype J] [Fintype I₁] [Fintype I₂] [Fintype J₁] [Fintype J₂]

noncomputable abbrev pair (x y : I → ℝ) := ∑ i, x i * y i

theorem pair_sum (a b : I₁ → ℝ) (c d : I₂ → ℝ) :
    pair (Sum.elim a c) (Sum.elim b d) = pair a b + pair c d := by
  simp [pair, Fintype.sum_sum_type]
theorem pair_scale (r s : ℝ) (a b : I → ℝ) :
    pair (r • a) (s • b) = r*s*pair a b := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros; ring

theorem norm_sum (a : I₁ → ℝ) (b : I₂ → ℝ) :
    sqNorm (Sum.elim a b) = sqNorm a + sqNorm b := by
  simp [sqNorm, Fintype.sum_sum_type]
theorem norm_scale (r : ℝ) (a : I → ℝ) : sqNorm (r • a) = r^2*sqNorm a := by
  simp [sqNorm, mul_pow, Finset.mul_sum]
@[simp] theorem norm_zero : sqNorm (0 : I → ℝ) = 0 := by simp [sqNorm]
@[simp] theorem pair_zero (a : I → ℝ) : pair a 0 = 0 := by simp [pair]
@[simp] theorem zero_pair (a : I → ℝ) : pair 0 a = 0 := by simp [pair]

theorem positive {P : SpanProgram m I J} {x : Fin m → Bool} {a : J → ℝ}
    (h : P.IsOneWitness x a) : P.Accepts x := by
  classical
  change P.target ∈ _
  rw [← h]
  have he : P.applyAvail x a = ∑ j, if (P.label j).avail x then a j • P.vec j else 0 := by
    ext i; simp [applyAvail, Finset.sum_apply, apply_ite (fun v : I → ℝ => v i)]
  rw [he]
  apply Submodule.sum_mem
  intro j _
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, rfl⟩)
  · exact Submodule.zero_mem _

theorem negative {P : SpanProgram m I J} {x : Fin m → Bool} {w : I → ℝ}
    (h : P.IsZeroWitness x w) : ¬ P.Accepts x := by
  intro ht
  let d : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, w i • LinearMap.proj i
  have hd (v : I → ℝ) : d v = pair w v := by simp [d, pair, LinearMap.sum_apply]
  have hker : Submodule.span ℝ (P.vec '' {j | (P.label j).avail x = true}) ≤ LinearMap.ker d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    exact (hd _).trans (h.2 j hj)
  have hh := LinearMap.mem_ker.mp (hker ht)
  linarith only [hh, hd P.target, h.1]

theorem assemble (P : SpanProgram m I J) (f : (Fin m → Bool) → Bool) {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (pos : ∀ x, f x = true → ∃ a, P.IsOneWitness x a ∧ sqNorm a ≤ A)
    (neg : ∀ x, f x = false → ∃ w, P.IsZeroWitness x w ∧ sqNorm w ≤ B) :
    P.Computes f ∧ P.HasWitnessParams A B := by
  have hc : P.Computes f := by
    intro x
    cases h : f x with
    | true => exact iff_of_true (positive (pos x h).choose_spec.1) rfl
    | false => exact iff_of_false (negative (neg x h).choose_spec.1) (by decide)
  exact ⟨hc, hA, hB, fun x => ⟨fun h => pos x ((hc x).mp h),
    fun h => neg x (Bool.eq_false_iff.mpr (fun hh => h ((hc x).mpr hh)))⟩⟩

theorem avail_scale (P : SpanProgram m I J) (x : Fin m → Bool) (r : ℝ) (a : J → ℝ) :
    P.applyAvail x (r • a) = r • P.applyAvail x a := by
  ext i
  simp only [applyAvail, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

@[simp] theorem avail_zero (P : SpanProgram m I J) (x : Fin m → Bool) :
    P.applyAvail x 0 = 0 := by ext i; simp [applyAvail]

/-- Transport a verified span program along bijections of coordinates and columns. -/
theorem reindex (P : SpanProgram m I₁ J₁) (Q : SpanProgram m I₂ J₂)
    (e : I₁ ≃ I₂) (g : J₁ ≃ J₂)
    (ht : ∀ i, Q.target (e i) = P.target i)
    (hv : ∀ j i, Q.vec (g j) (e i) = P.vec j i)
    (hl : ∀ j, Q.label (g j) = P.label j)
    (f : (Fin m → Bool) → Bool) (A B : ℝ)
    (vf : P.IsVectorForm) (hc : P.Computes f) (hw : P.HasWitnessParams A B) :
    Q.IsVectorForm ∧ Q.Computes f ∧ Q.HasWitnessParams A B := by
  classical
  have hn {α β : Type} [Fintype α] [Fintype β] (u : α ≃ β)
      (v : β → ℝ) : sqNorm v = sqNorm (fun a => v (u a)) := by
    exact (u.sum_comp (fun b => v b ^ 2)).symm
  refine ⟨⟨?_,?_⟩, assemble Q f hw.1 hw.2.1 ?_ ?_⟩
  · rw [hn e]; simpa only [ht] using vf.1
  · intro k
    obtain ⟨j,rfl⟩ := g.surjective k
    rw [hn e]; simpa only [hv] using vf.2 j
  · intro x hx
    obtain ⟨a,ha,hnorm⟩ := (hw.2.2 x).1 ((hc x).mpr hx)
    refine ⟨a ∘ g.symm, ?_, ?_⟩
    · funext i
      obtain ⟨i,rfl⟩ := e.surjective i
      change (∑ j, if (Q.label j).avail x then a (g.symm j) * Q.vec j (e i) else 0) = _
      rw [← g.sum_comp,ht]
      simp only [hl,hv,Equiv.symm_apply_apply]
      convert congrFun ha i using 1 <;> rfl
    · rw [hn g]; simpa using hnorm
  · intro x hx
    obtain ⟨w,hw',hnorm⟩ := (hw.2.2 x).2 (fun h => by simpa [hx] using (hc x).mp h)
    refine ⟨w ∘ e.symm, ⟨?_,?_⟩,?_⟩
    · rw [← e.sum_comp]
      simpa only [Function.comp_apply,Equiv.symm_apply_apply,ht] using hw'.1
    · intro j hj
      obtain ⟨j,rfl⟩ := g.surjective j
      rw [← e.sum_comp]
      simp only [hl] at hj
      simpa only [Function.comp_apply,Equiv.symm_apply_apply,hv] using hw'.2 j hj
    · rw [hn e]; simpa using hnorm

noncomputable def extension (P : SpanProgram m I J) (c s : ℝ) :
    SpanProgram m (I ⊕ Unit) (J ⊕ Unit) where
  target := Sum.elim 0 1
  vec := Sum.elim (fun j => Sum.elim (P.vec j) 0)
    (fun _ => Sum.elim ((-s) • P.target) (fun _ => c))
  label := Sum.elim P.label (fun _ => Label.always)

theorem ext_avail (P : SpanProgram m I J) (c s : ℝ) (x : Fin m → Bool) (a : J → ℝ) (u : ℝ) :
    (extension P c s).applyAvail x (Sum.elim a (fun _ => u)) =
      Sum.elim (P.applyAvail x a + (-u*s) • P.target) (fun _ => u*c) := by
  ext i; cases i with
  | inl i =>
    simp [extension,applyAvail,Label.avail,Fintype.sum_sum_type,mul_assoc] <;> rfl
  | inr i =>
    simp [extension,applyAvail,Label.avail,Fintype.sum_sum_type] <;> rfl

theorem extension_spec (P : SpanProgram m I J) (A B : ℝ)
    (f : (Fin m → Bool) → Bool) (v : P.IsVectorForm) (hc : P.Computes f)
    (hw : P.HasWitnessParams A B) :
    let c := (connAngle A B).1
    let s := (connAngle A B).2
    (extension P c s).IsVectorForm ∧ (extension P c s).Computes f ∧
      (extension P c s).HasBalancedBound (1 + Real.sqrt ((A+1)*B)) := by
  classical
  dsimp only
  let t := Real.sqrt (B / (A+1))
  let c := (connAngle A B).1
  let s := (connAngle A B).2
  have hA := hw.1
  have hB := hw.2.1
  have hAp : 0 < A+1 := by linarith
  have hBp : 0 < B := by linarith
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hBp hAp)
  have ht2 : t^2*(A+1) = B := (eq_div_iff hAp.ne').mp (Real.sq_sqrt (div_nonneg hBp.le hAp.le))
  have htp : 0 < 1+t := by linarith
  have hcp : 0 < c := Real.sqrt_pos.mpr (div_pos one_pos htp)
  have hsp : 0 < s := Real.sqrt_pos.mpr (div_pos ht htp)
  have hc2 : c^2*(1+t) = 1 := (eq_div_iff htp.ne').mp (Real.sq_sqrt (div_nonneg zero_le_one htp.le))
  have hs2 : s^2*(1+t) = t := (eq_div_iff htp.ne').mp (Real.sq_sqrt (div_nonneg ht.le htp.le))
  have hcs : c^2+s^2 = 1 := by apply (mul_right_cancel₀ htp.ne'); nlinarith
  have hratio : s^2 = c^2*t := by apply (mul_right_cancel₀ htp.ne'); linear_combination hs2 - t * hc2
  have hrs : Real.sqrt ((A+1)*B) = (A+1)*t := by
    rw [← Real.sqrt_sq (mul_nonneg hAp.le ht.le)]
    congr 1
    linear_combination -(A+1)*ht2
  have hvec : (extension P c s).IsVectorForm := by
    constructor
    · change sqNorm (Sum.elim (0 : I → ℝ) (1 : Unit → ℝ)) = 1
      rw [norm_sum,norm_zero]; simp [sqNorm]
    · rintro (j|u)
      · change sqNorm (Sum.elim (P.vec j) (0 : Unit → ℝ)) = 1
        rw [norm_sum,norm_zero,v.2]; ring
      · change sqNorm (Sum.elim ((-s) • P.target) (fun _ : Unit => c)) = 1
        rw [norm_sum,norm_scale,v.1]
        simp only [sqNorm,Fintype.sum_unique]; nlinarith only [hcs]
  refine ⟨hvec, assemble (extension P c s) f (by linarith [Real.sqrt_nonneg ((A+1)*B)])
    (by linarith [Real.sqrt_nonneg ((A+1)*B)]) ?_ ?_⟩
  · intro x hx
    obtain ⟨a,ha,hn⟩ := (hw.2.2 x).1 ((hc x).mpr hx)
    refine ⟨Sum.elim ((s/c) • a) (fun _ => c⁻¹), ?_, ?_⟩
    · unfold IsOneWitness at ha ⊢
      rw [ext_avail,avail_scale,ha]
      change Sum.elim (_ + _) _ = Sum.elim (0 : I → ℝ) (1 : Unit → ℝ)
      funext i
      cases i <;> simp [hcp.ne',div_eq_mul_inv] <;> ring
    · rw [norm_sum,norm_scale,hrs]
      have H := mul_le_mul_of_nonneg_left hn (sq_nonneg (s/c))
      calc
        _ ≤ (s/c)^2*A+c⁻¹^2 := by simpa only [sqNorm,Fintype.sum_unique] using add_le_add_left H (c⁻¹^2)
        _ = 1+(A+1)*t := by field_simp [hcp.ne']; linear_combination A*hratio - hc2
  · intro x hx
    obtain ⟨w,hw',hn⟩ := (hw.2.2 x).2 (fun h => by simpa [hx] using (hc x).mp h)
    refine ⟨Sum.elim ((c/s) • w) (1 : Unit → ℝ), ⟨?_,?_⟩,?_⟩
    · change pair (Sum.elim ((c/s) • w) (1 : Unit → ℝ)) (Sum.elim 0 1) = 1
      rw [pair_sum,pair_zero]; simp [pair]
    · rintro (j|u) hj
      · change pair (Sum.elim ((c/s) • w) (1 : Unit → ℝ)) (Sum.elim (P.vec j) 0) = 0
        rw [pair_sum,pair_zero,← one_smul ℝ (P.vec j),pair_scale,show pair w (P.vec j) = 0 from hw'.2 j hj]; ring
      · change pair (Sum.elim ((c/s) • w) (1 : Unit → ℝ))
          (Sum.elim ((-s) • P.target) (fun _ => c)) = 0
        rw [pair_sum,pair_scale,show pair w P.target = 1 from hw'.1]
        simp [pair,hsp.ne']
    · rw [norm_sum,norm_scale,hrs]
      have H := mul_le_mul_of_nonneg_left hn (sq_nonneg (c/s))
      calc
        _ ≤ (c/s)^2*B+1 := by simpa only [sqNorm,Fintype.sum_unique,Pi.one_apply,one_pow] using add_le_add_left H 1
        _ = 1+(A+1)*t := by field_simp [hsp.ne']; linear_combination -c^2*ht2 - ((A+1)*t)*hratio
end HelperProof

namespace HelperProof
variable {m : ℕ}

noncomputable def addPoint {α : Type} [DecidableEq α] (s u : Finset α) (z : α)
    (hz : z ∉ s) (h : u = insert z s) : (s ⊕ Unit) ≃ u where
  toFun := Sum.elim (fun a => ⟨a.val, h ▸ Finset.mem_insert_of_mem a.property⟩)
    (fun _ => ⟨z, h ▸ Finset.mem_insert_self _ _⟩)
  invFun a := if hh : a.val = z then .inr () else
    .inl ⟨a.val, (Finset.mem_insert.mp (h ▸ a.property)).resolve_left hh⟩
  left_inv := by
    rintro (a|u)
    · simp [show a.val ≠ z from fun he => hz (he ▸ a.property)]
    · cases u; simp
  right_inv := by
    intro a; dsimp only; split_ifs with ha
    · exact Subtype.ext ha.symm
    · rfl

private theorem fresh_coord (tie : TieRule) (T : Formula m) : Coord.helper [] ∉ chainCoords tie T := by
  have hf (d : Bool) (k : Coord) : Coord.cons d k ≠ .helper [] := by cases k <;> simp [Coord.cons]
  cases T <;> simp [chainCoords,coordsStep,hf]
private theorem fresh_col (tie : TieRule) (T : Formula m) : Col.conn [] ∉ chainCols tie T := by
  have hf (d : Bool) (j : Col) : Col.cons d j ≠ .conn [] := by cases j <;> simp [Col.cons]
  cases T <;> simp [chainCols,colsStep,hf]

private theorem leaflessU (tie : TieRule) (T : Formula m) : chainU tie T (.helper []) = 0 := by
  cases T <;> simp [chainU,uStep,liftV,Coord.uncons,basisV]

private theorem oldAtHelper (tie : TieRule) (T : Formula m) (j : Col) (hj : j ≠ .conn []) :
    colVec tie T j (.helper []) = 0 := by
  cases T with
  | lit i b => by_cases h : j = .lit [] <;> simp [colVec,h,basisV]
  | and U V | or U V =>
    cases j with
    | lit p => cases p <;> simp [colVec,colStep,Col.uncons,topCol,liftV,Coord.uncons]
    | rot p => cases p <;> simp [colVec,colStep,Col.uncons,topCol,liftV,Coord.uncons]
    | conn p => cases p <;> simp_all [colVec,colStep,Col.uncons,topCol,liftV,Coord.uncons]

private theorem connectorVec (tie : TieRule) (T : Formula m) (hT : T.isLeaf = false) (k : Coord) :
    colVec tie T (.conn []) k = (connAngle (chainParams tie T).1 (chainParams tie T).2).1 * basisV (.helper []) k -
      (connAngle (chainParams tie T).1 (chainParams tie T).2).2 * chainU tie T k := by
  cases T <;> first | rfl | contradiction

private theorem connectorLabel (T : Formula m) (hT : T.isLeaf = false) : colLabel T (.conn []) = Label.always := by
  cases T <;> first | rfl | contradiction
end HelperProof

open HelperProof

theorem solution {m : ℕ} (tie : TieRule) (T : Formula m) (hT : T.isLeaf = false)
    (hterm : ∀ t ∈ terminals tie T,
      (program t.1 t.2).IsVectorForm ∧ (program t.1 t.2).Computes t.2.eval ∧
        (program t.1 t.2).HasBalancedBound (helperBound t.1 t.2)) :
    (program tie T).Computes T.eval ∧
      (program tie T).IsVectorForm ∧
      (∀ k, (program tie T).target k = basisV (.helper []) k.1) ∧
      (program tie T).HasBalancedBound (helperBound tie T) ∧
      helperBound tie T = 1 + Real.sqrt
        ((terminals tie T).map (fun t => helperBound t.1 t.2 ^ 2 + helperBound t.1 t.2)).sum := by
  obtain ⟨hc,hv,hw,hs,_,_⟩ := lemma_5_5 tie T hT hterm
  let A := (chainParams tie T).1
  let B := (chainParams tie T).2
  let c := (connAngle A B).1
  let s := (connAngle A B).2
  let P := chainProgram tie T
  let Q := program tie T
  have hI : fullCoords tie T = insert (.helper []) (chainCoords tie T) := by
    simp [fullCoords,fullCoordsOf,hT]
  have hJ : fullCols tie T = insert (.conn []) (chainCols tie T) := by
    simp [fullCols,fullColsOf,hT]
  let e := addPoint _ _ _ (fresh_coord tie T) hI
  let g := addPoint _ _ _ (fresh_col tie T) hJ
  have ez (k : chainCoords tie T) : k.val ≠ .helper [] :=
    fun h => fresh_coord tie T (h ▸ k.property)
  have gz (j : chainCols tie T) : j.val ≠ .conn [] :=
    fun h => fresh_col tie T (h ▸ j.property)
  have heq (i) : Q.target i = basisV (.helper []) i.val := by simp [Q,program,exportV,exportKey,hT]
  obtain ⟨v',hc',hw'⟩ := extension_spec P A B T.eval hv hc hw
  have ht' (i) : Q.target (e i) = (extension P c s).target i := by
    rw [heq]
    cases i with
    | inl k => change basisV (.helper []) k.val = 0; simp [basisV,ez]
    | inr u => change basisV (.helper []) (.helper []) = 1; simp [basisV]
  have hvec (j i) : Q.vec (g j) (e i) = (extension P c s).vec j i := by
    cases j with
    | inl j =>
      cases i with
      | inl k => rfl
      | inr u => exact oldAtHelper tie T j.val (gz j)
    | inr u =>
      cases i with
      | inl k =>
        change colVec tie T (.conn []) k.val = -s * chainU tie T k.val
        rw [connectorVec tie T hT]
        simp [basisV,ez,s,A,B]
      | inr v =>
        change colVec tie T (.conn []) (.helper []) = c
        rw [connectorVec tie T hT,leaflessU]
        simp [basisV,c,A,B]
  have hl (j) : Q.label (g j) = (extension P c s).label j := by
    cases j with
    | inl j => rfl
    | inr u => exact connectorLabel T hT
  obtain ⟨v'',hc'',hw''⟩ := reindex (extension P c s) Q e g ht' hvec hl _ _ _ v' hc' hw'
  have hB : helperBound tie T = 1 + Real.sqrt ((A+1)*B) := by simp [helperBound,helperBoundOf,hT,A,B]
  exact ⟨hc'',v'',heq,hB ▸ hw'',by rw [hB]; change 1 + Real.sqrt _ = _; rw [show (A+1)*B = _ from hs]⟩
