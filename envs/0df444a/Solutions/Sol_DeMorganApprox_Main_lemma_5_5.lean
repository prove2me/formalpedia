-- Prove2me | solution 1 for DeMorganApprox.Main.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:24:09.379189+00:00
-- url     : https://prove2.me/submissions/01e29360-7a61-44af-bdab-e25e77a0be47

import Definitions.Def_DeMorganApprox_Main_HeavyChains
import Theorems.Thm_DeMorganApprox_Main_lemma_5_3
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


end HelperProof
namespace ChainReindex
variable {m : ℕ}
@[simp] private lemma unc_coord (d : Bool) (k : Coord) : (k.cons d).uncons = some (d,k) := by cases k <;> rfl
@[simp] private lemma unc_col (d : Bool) (j : Col) : (j.cons d).uncons = some (d,j) := by cases j <;> rfl
@[simp] private lemma coord_cons_ne_top (d : Bool) (k : Coord) : k.cons d ≠ .helper [] := by cases k <;> simp [Coord.cons]
@[simp] private lemma col_cons_ne_rot (d : Bool) (j : Col) : j.cons d ≠ .rot [] := by cases j <;> simp [Col.cons]
@[simp] private lemma col_cons_ne_conn (d : Bool) (j : Col) : j.cons d ≠ .conn [] := by cases j <;> simp [Col.cons]

@[simp] private lemma lift_cons (d e : Bool) (v : Coord → ℝ) (k : Coord) :
    liftV d v (k.cons e) = if e = d then v k else 0 := by simp [liftV]

private lemma pass_col (g d : Bool) (t : TieRule) (p q : Formula m) (j : Col) :
    colVec t (mkGate g p q) (j.cons d) =
      liftV d (colVec (t.sub d) (pick d p q) j) := by
  cases g <;> cases d <;> simp [mkGate,pick,colVec,colStep]

private noncomputable abbrev ang (g : Bool) (t : TieRule) (p q : Formula m) :=
  nodeAngle g t p q (chainParams (t.sub false) p) (chainParams (t.sub true) q)

private lemma u_exp (g : Bool) (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    chainU t (mkGate g p q) =
      (ang g t p q).1 • liftV d (chainU (t.sub d) (pick d p q)) +
      (ang g t p q).2 • liftV (!d) (exportV (pick (!d) p q)) := by
  cases hd : heavyDir t p q <;> cases g <;>
    simp [ang,mkGate,chainU,uStep,hd,pick]

private lemma rot_exp (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    colVec t (mkGate true p q) (.rot []) =
      (ang true t p q).2 • liftV d (chainU (t.sub d) (pick d p q)) -
      (ang true t p q).1 • liftV (!d) (exportV (pick (!d) p q)) := rfl

private lemma gateCols (g : Bool) (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    chainCols t (mkGate g p q) =
      ((chainCols (t.sub d) (pick d p q)).image (Col.cons d) ∪
      (fullCols (t.sub (!d)) (pick (!d) p q)).image (Col.cons (!d))) ∪
      (if g then {.rot []} else ∅) := by
  cases hd : heavyDir t p q <;> cases g <;> simp [mkGate, chainCols,colsStep,hd,pick,fullCols]

private lemma gateCoords (g : Bool) (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    chainCoords t (mkGate g p q) =
      (chainCoords (t.sub d) (pick d p q)).image (Coord.cons d) ∪
      (fullCoords (t.sub (!d)) (pick (!d) p q)).image (Coord.cons (!d)) := by
  cases hd : heavyDir t p q <;> cases g <;> simp [mkGate, chainCoords,coordsStep,hd,pick,fullCoords]

private noncomputable def dualEquiv {α : Type} [DecidableEq α] (push : Bool → α → α)
    (unpush : α → Option (Bool × α)) (inv : ∀ d a, unpush (push d a) = some (d,a))
    (d : Bool) (H L D : Finset α) (he : D = H.image (push d) ∪ L.image (push (!d))) :
    (H ⊕ L) ≃ D := by
  classical
  let f : H ⊕ L → D := Sum.elim
    (fun h => ⟨push d h, he ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem _ h.property)⟩)
    (fun l => ⟨push (!d) l, he ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem _ l.property)⟩)
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    have eq := congrArg (fun k : D => unpush k.val) h
    cases a <;> cases b <;> simp [f, inv] at eq ⊢ <;> aesop
  · rintro ⟨k,hk⟩
    rw [he] at hk
    rcases Finset.mem_union.mp hk with h|h <;> obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h
    · exact ⟨.inl ⟨v,hv⟩,rfl⟩
    · exact ⟨.inr ⟨v,hv⟩,rfl⟩

@[simp] private theorem dual_inl {α : Type} [DecidableEq α] {push : Bool → α → α}
    {unpush : α → Option (Bool × α)} {inv : ∀ d a, unpush (push d a) = some (d,a)}
    {d : Bool} {H L D : Finset α} {he : D = H.image (push d) ∪ L.image (push (!d))}
    (h : H) : (dualEquiv push unpush inv d H L D he (.inl h)).val = push d h := rfl
@[simp] private theorem dual_inr {α : Type} [DecidableEq α] {push : Bool → α → α}
    {unpush : α → Option (Bool × α)} {inv : ∀ d a, unpush (push d a) = some (d,a)}
    {d : Bool} {H L D : Finset α} {he : D = H.image (push d) ∪ L.image (push (!d))}
    (l : L) : (dualEquiv push unpush inv d H L D he (.inr l)).val = push (!d) l := rfl

private noncomputable def plusRot {I : Type} (D J : Finset Col) (e : I ≃ D)
    (hD : Col.rot [] ∉ D) (hJ : J = D ∪ {.rot []}) : (I ⊕ Unit) ≃ J := by
  let f : I ⊕ Unit → J := Sum.elim
    (fun x => ⟨(e x).val,hJ ▸ Finset.mem_union_left _ (e x).property⟩)
    (fun _ => ⟨.rot [],by simp [hJ]⟩)
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (e.injective (Subtype.ext he))
      | inr j =>
        change (e i).val = .rot [] at he
        exact (hD (he ▸ (e i).property)).elim
    | inr u =>
      cases y with
      | inl j =>
        change Col.rot [] = (e j).val at he
        exact (hD (he.symm ▸ (e j).property)).elim
      | inr v => rfl
  · rintro ⟨k,hk⟩
    rw [hJ,Finset.mem_union,Finset.mem_singleton] at hk
    rcases hk with h|rfl
    · exact ⟨.inl (e.symm ⟨k,h⟩),Subtype.ext (congrArg (fun x : D => x.val) (e.apply_symm_apply ⟨k,h⟩))⟩
    · exact ⟨.inr (),rfl⟩
@[simp] private lemma rot_inl {I : Type} {D J : Finset Col} {e : I ≃ D}
    {hD : Col.rot [] ∉ D} {hJ : J = D ∪ {.rot []}} (i : I) :
    (plusRot D J e hD hJ (.inl i)).val = (e i).val := rfl
@[simp] private lemma rot_inr {I : Type} {D J : Finset Col} {e : I ≃ D}
    {hD : Col.rot [] ∉ D} {hJ : J = D ∪ {.rot []}} (u : Unit) :
    (plusRot D J e hD hJ (.inr u)).val = .rot [] := rfl

private lemma pass_label (g d : Bool) (p q : Formula m) (j : Col) :
    colLabel (mkGate g p q) (j.cons d) = colLabel (pick d p q) j := by
  cases g <;> cases d <;> simp [mkGate,colLabel,pick]

private lemma angle_at (g : Bool) (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    let par := chainParams (t.sub d) (pick d p q)
    let S := helperBound (t.sub (!d)) (pick (!d) p q)
    ang g t p q = gateAngle g par.1 par.2 S S := by
  cases h : heavyDir t p q <;> simp [ang,nodeAngle,h,pick,helperBound]

def Transfer {I₁ I₂ J₁ J₂ : Type} [Fintype I₁] [Fintype I₂] [Fintype J₁] [Fintype J₂]
    (P : SpanProgram m I₁ J₁) (Q : SpanProgram m I₂ J₂) := ∀ f A B,
    P.IsVectorForm → P.Computes f → P.HasWitnessParams A B →
      Q.IsVectorForm ∧ Q.Computes f ∧ Q.HasWitnessParams A B


theorem gateTransferAnd (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    let H := pick d p q
    let L := pick (!d) p q
    let PH := chainProgram (t.sub d) H
    let PL := program (t.sub (!d)) L
    let par := chainParams (t.sub d) H
    let S := helperBound (t.sub (!d)) L
    Transfer (PH.andCompose PL par.2 S) (chainProgram t (.and p q)) := by
  let d := heavyDir t p q
  let H := pick d p q
  let L := pick (!d) p q
  let T := mkGate false p q
  let A := chainCoords (t.sub d) H
  let B := fullCoords (t.sub (!d)) L
  let J := chainCols (t.sub d) H
  let K := fullCols (t.sub (!d)) L
  let rows := dualEquiv Coord.cons Coord.uncons unc_coord d A B (chainCoords t T) (gateCoords false t p q)
  let E := J.image (Col.cons d) ∪ K.image (Col.cons (!d))

  have hE : chainCols t T = E := by
    simpa [T,E,J,K,H,L,d] using gateCols false t p q
  let cols := dualEquiv Col.cons Col.uncons unc_col d J K (chainCols t T) hE

  dsimp only
  intro f a b vf hc hw
  refine HelperProof.reindex _ (chainProgram t T) rows cols ?_ ?_ ?_ f a b vf hc hw
  · intro i
    cases i <;> simp only [chainProgram, rows,dual_inl,dual_inr,SpanProgram.andCompose,Sum.elim_inl,Sum.elim_inr,
      Pi.smul_apply,smul_eq_mul,program]
      <;> change chainU t (mkGate false p q) _ = _
      <;> rw [u_exp,angle_at]
      <;> simp [d,H,L,gateAngle]
  · intro j i
    cases j <;> cases i <;>
      simp only [chainProgram,program,SpanProgram.andCompose, cols,rows,dual_inl,dual_inr,
        Sum.elim_inl,Sum.elim_inr] <;>
      simp [T,pass_col,lift_cons,H,L,d]
  · intro j
    cases j <;>
      simp [chainProgram,program,SpanProgram.andCompose,cols,T,pass_label,H,L,d]

theorem gateTransferOr (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    let H := pick d p q
    let L := pick (!d) p q
    let PH := chainProgram (t.sub d) H
    let PL := program (t.sub (!d)) L
    let par := chainParams (t.sub d) H
    let S := helperBound (t.sub (!d)) L
    Transfer (PH.orCompose PL par.1 S) (chainProgram t (.or p q)) := by
  let d := heavyDir t p q
  let H := pick d p q
  let L := pick (!d) p q
  let T := mkGate true p q
  let A := chainCoords (t.sub d) H
  let B := fullCoords (t.sub (!d)) L
  let J := chainCols (t.sub d) H
  let K := fullCols (t.sub (!d)) L
  let rows := dualEquiv Coord.cons Coord.uncons unc_coord d A B (chainCoords t T) (gateCoords true t p q)
  let E := J.image (Col.cons d) ∪ K.image (Col.cons (!d))

  let base := dualEquiv Col.cons Col.uncons unc_col d J K E rfl
  have hrot : Col.rot [] ∉ E := by
    simp [E, Finset.mem_union, Finset.mem_image, col_cons_ne_rot]
  let cols := plusRot E (chainCols t T) base hrot (gateCols true t p q)

  dsimp only
  intro f a b vf hc hw
  refine HelperProof.reindex _ (chainProgram t T) rows cols ?_ ?_ ?_ f a b vf hc hw
  · intro i
    cases i <;> simp only [chainProgram, rows,dual_inl,dual_inr,SpanProgram.orCompose,Sum.elim_inl,Sum.elim_inr,
      Pi.smul_apply,smul_eq_mul,program]
      <;> change chainU t (mkGate true p q) _ = _
      <;> rw [u_exp,angle_at]
      <;> simp [d,H,L,gateAngle]
  · intro j i
    rcases j with j|u
    · cases j <;> cases i <;>
        simp only [chainProgram,program,SpanProgram.orCompose, cols,base,rows,rot_inl,dual_inl,dual_inr,
          Sum.elim_inl,Sum.elim_inr] <;>
        simp [T,pass_col,lift_cons,H,L,d]
    · cases i <;>
        simp only [chainProgram,program,SpanProgram.orCompose,cols,rot_inr,rows,dual_inl,dual_inr,
          Sum.elim_inl,Sum.elim_inr,Pi.smul_apply,smul_eq_mul] <;>
        simp [T,rot_exp,angle_at,gateAngle,lift_cons,d,H,L]
  · intro j
    rcases j with j|u
    · cases j <;>
        simp [chainProgram,program,SpanProgram.orCompose,cols,base,rot_inl,T,pass_label,H,L,d]
    · rfl

end ChainReindex

namespace ChainReindex

private abbrev GoodTerminal {m : ℕ} (t : TieRule × Formula m) : Prop :=
  (program t.1 t.2).IsVectorForm ∧ (program t.1 t.2).Computes t.2.eval ∧
    (program t.1 t.2).HasBalancedBound (helperBound t.1 t.2)

private abbrev GoodChain {m : ℕ} (t : TieRule) (T : Formula m) : Prop :=
  (chainProgram t T).IsVectorForm ∧ (chainProgram t T).Computes T.eval ∧
    (chainProgram t T).HasWitnessParams (chainParams t T).1 (chainParams t T).2

private theorem step {m : ℕ} (t : TieRule) (p q : Formula m) (g : Bool)
    (iH : GoodChain (t.sub (heavyDir t p q)) (pick (heavyDir t p q) p q))
    (iL : GoodTerminal (t.sub (!heavyDir t p q),pick (!heavyDir t p q) p q)) :
    GoodChain t (mkGate g p q) := by
  let d := heavyDir t p q
  let H := pick d p q
  let L := pick (!d) p q
  let P := chainProgram (t.sub d) H
  let Q := program (t.sub (!d)) L
  let par := chainParams (t.sub d) H
  let S := helperBound (t.sub (!d)) L
  have ⟨hp,hf,hw⟩ := iH
  have ⟨hq,hg,hu⟩ := iL
  have ⟨hOr,hAnd⟩ := lemma_5_3 P Q H.eval L.eval par.1 par.2 S S hp hq hf hg hw hu
  have hpar : nodeParams g t p q (chainParams (t.sub false) p) (chainParams (t.sub true) q)
      = gateParams g par.1 par.2 S S := by
    cases he : heavyDir t p q <;> simp [nodeParams,par,S,H,L,d,he,pick,helperBound]
  cases g with
  | false =>
    have ht := gateTransferAnd t p q (fun x => H.eval x && L.eval x)
      (andParams par.1 par.2 S S).1 (andParams par.1 par.2 S S).2 hAnd.2.1 hAnd.1 hAnd.2.2.2.2.2.1
    have he : (fun x => H.eval x && L.eval x) = (Formula.and p q).eval := by
      funext x; cases hh : heavyDir t p q <;> simp [H,L,d,hh,pick,Formula.eval,Bool.and_comm]
    rw [he] at ht
    have eqpar : chainParams t (Formula.and p q) = andParams par.1 par.2 S S := hpar
    change GoodChain t (Formula.and p q)
    exact ⟨ht.1,ht.2.1,by rw [eqpar]; exact ht.2.2⟩
  | true =>
    have ht := gateTransferOr t p q (fun x => H.eval x || L.eval x)
      (orParams par.1 par.2 S S).1 (orParams par.1 par.2 S S).2 hOr.2.1 hOr.1 hOr.2.2.2.2.2.2.1
    have he : (fun x => H.eval x || L.eval x) = (Formula.or p q).eval := by
      funext x; cases hh : heavyDir t p q <;> simp [H,L,d,hh,pick,Formula.eval,Bool.or_comm]
    rw [he] at ht
    have eqpar : chainParams t (Formula.or p q) = orParams par.1 par.2 S S := hpar
    change GoodChain t (Formula.or p q)
    exact ⟨ht.1,ht.2.1,by rw [eqpar]; exact ht.2.2⟩

theorem chainSemantics {m : ℕ} (t : TieRule) (T : Formula m)
    (hterm : ∀ z ∈ terminals t T, GoodTerminal z) : GoodChain t T := by
  induction T generalizing t with
  | lit i b =>
    exact hterm (t,Formula.lit i b) (by simp [terminals])
  | and p q ip iq | or p q ip iq =>
    simp only [terminals,List.forall_mem_cons] at hterm
    first | apply step t p q false _ hterm.1 | apply step t p q true _ hterm.1
    cases hd : heavyDir t p q <;> simp only [hd,Bool.false_eq_true,if_false,ite_true,pick] at *
    · exact ip _ hterm.2
    · exact iq _ hterm.2
end ChainReindex

namespace ChainTail

variable {m : ℕ}

private lemma angle_ok {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Real.sqrt (a / (a+b)) ∧ 0 ≤ Real.sqrt (b / (a+b)) ∧
    (Real.sqrt (a / (a+b)))^2 + (Real.sqrt (b / (a+b)))^2 ≤ 1 := by
  refine ⟨Real.sqrt_nonneg _,Real.sqrt_nonneg _,?_⟩
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ←add_div]
  rcases eq_or_ne (a+b) 0 with h|h <;> simp [h]

private lemma params_nonneg (tie : TieRule) (T : Formula m) :
    0 ≤ (chainParams tie T).1 ∧ 0 ≤ (chainParams tie T).2 := by
  have aux {g : Bool} {t : TieRule} {p q : ℝ × ℝ} {φ ψ : Formula m}
      (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) (hq : 0 ≤ q.1 ∧ 0 ≤ q.2) :
      0 ≤ (nodeParams g t φ ψ p q).1 ∧ 0 ≤ (nodeParams g t φ ψ p q).2 := by
    have hs (L : Formula m) (v : ℝ × ℝ) : 0 ≤ helperBoundOf L v := by
      unfold helperBoundOf
      split <;> positivity
    rcases hp with ⟨hp,hp'⟩
    rcases hq with ⟨hq,hq'⟩
    have hsl := hs φ p
    have hsr := hs ψ q
    cases hd : heavyDir t φ ψ <;> cases g <;>
      simp only [nodeParams, hd, gateParams, andParams, orParams, Bool.false_eq_true, if_true, if_false] <;>
      simp only [Bool.not_true, Bool.not_false, pick, if_true, Bool.false_eq_true, if_false] <;> constructor <;> positivity
  induction T generalizing tie with
  | lit => exact ⟨by norm_num [chainParams],by norm_num [chainParams]⟩
  | and p q hp hq => exact aux (hp _) (hq _)
  | or p q hp hq => exact aux (hp _) (hq _)

private def OK (v : ℝ × ℝ) := 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1^2 + v.2^2 ≤ 1

private lemma node_ok (g : Bool) (t : TieRule) (φ ψ : Formula m) :
    OK (nodeAngle g t φ ψ (chainParams (t.sub false) φ) (chainParams (t.sub true) ψ)) := by
  unfold nodeAngle
  dsimp only
  generalize h : heavyDir t φ ψ = d
  have hs (L : Formula m) (v : ℝ × ℝ) : 0 ≤ helperBoundOf L v := by
    unfold helperBoundOf
    split <;> positivity
  have hor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : OK (orAngle a b) := by
    simpa [OK, orAngle, show a + b + 2 = (a+1)+(b+1) by ring] using
      angle_ok (a := a+1) (b := b+1) (by positivity) (by positivity)
  have hand {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : OK (andAngle a b) := angle_ok ha hb
  cases d <;> cases g <;> simp only [gateAngle, Bool.false_eq_true, if_true, if_false] <;>
    first | exact hand (params_nonneg _ _).2 (hs _ _) | exact hor (params_nonneg _ _).1 (hs _ _)

lemma chain_nonneg (t : TieRule) (T : Formula m) (k : Coord) : 0 ≤ chainU t T k := by
  have bas (j k : Coord) : 0 ≤ basisV j k := by simp [basisV]; split <;> norm_num
  have lift {v : Coord → ℝ} (hv : ∀ k, 0 ≤ v k) (d : Bool) (k : Coord) : 0 ≤ liftV d v k := by
    simp only [liftV]; split <;> try positivity
    split <;> first | apply hv | positivity
  have step (t : TieRule) (k : Coord) (g : Bool) (p q : Formula m) (hp : ∀ t k, 0 ≤ chainU t p k) (hq : ∀ t k, 0 ≤ chainU t q k) :
      0 ≤ uStep g t p q (chainU (t.sub false) p) (chainU (t.sub true) q) k := by
    obtain ⟨hc,hs,_⟩ := node_ok g t p q
    simp only [uStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply add_nonneg (mul_nonneg hc (lift _ _ _)) (mul_nonneg hs (lift (bas _) _ _))
    intro j
    split <;> first | apply hp | apply hq
  induction T generalizing t k with
  | lit i b => exact bas _ _
  | and p q hp hq => exact step t k false p q hp hq
  | or p q hp hq => exact step t k true p q hp hq



private lemma product_gate (g : Bool) (t : TieRule) (p q : Formula m) :
    let d := heavyDir t p q
    let h := chainParams (t.sub d) (pick d p q)
    let S := helperBound (t.sub (!d)) (pick (!d) p q)
    let v := chainParams t (mkGate g p q)
    (v.1+1)*v.2 = (h.1+1)*h.2 + (S^2+S) := by
  have aux (g : Bool) (A B S : ℝ) (ha : 0 ≤ A) (hb : 0 ≤ B) (hs : 0 < S) :
      let v := gateParams g A B S S
      (v.1+1)*v.2 = (A+1)*B + (S^2+S) := by
    have hd₁ : B+S ≠ 0 := by positivity
    have hd₂ : A+S+2 ≠ 0 := by positivity
    cases g <;> simp only [gateParams,Bool.false_eq_true,if_false,if_true,andParams,orParams]
    · field_simp
      <;> ring
    · field_simp
      <;> ring
  have hsp (e : Bool) : 0 < helperBound (t.sub e) (pick e p q) := by
    unfold helperBound helperBoundOf
    split <;> positivity
  let d := heavyDir t p q
  have h := aux g (chainParams (t.sub d) (pick d p q)).1 (chainParams (t.sub d) (pick d p q)).2
    (helperBound (t.sub (!d)) (pick (!d) p q)) (params_nonneg _ _).1 (params_nonneg _ _).2 (hsp _)
  cases hd : heavyDir t p q <;> cases g <;>
    simpa [d,hd,mkGate,chainParams,nodeParams,pick,helperBound] using h

lemma chain_product (t : TieRule) (T : Formula m) :
    ((chainParams t T).1+1)*(chainParams t T).2 =
    ((terminals t T).map (fun j => helperBound j.1 j.2 ^ 2 + helperBound j.1 j.2)).sum := by
  have step (g : Bool) (t : TieRule) (p q : Formula m)
      (hp : ∀ t, ((chainParams t p).1+1)*(chainParams t p).2 =
        ((terminals t p).map (fun j => helperBound j.1 j.2^2+helperBound j.1 j.2)).sum)
      (hq : ∀ t, ((chainParams t q).1+1)*(chainParams t q).2 =
        ((terminals t q).map (fun j => helperBound j.1 j.2^2+helperBound j.1 j.2)).sum) :
      ((chainParams t (mkGate g p q)).1+1)*(chainParams t (mkGate g p q)).2 =
      ((terminals t (mkGate g p q)).map (fun j => helperBound j.1 j.2^2+helperBound j.1 j.2)).sum := by
    rw [product_gate]
    cases hd : heavyDir t p q <;> cases g <;>
      simp only [hd,mkGate,terminals,pick,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        if_false,if_true,List.map_cons,List.sum_cons,hp,hq] <;> ring
  induction T generalizing t with
  | lit i b => norm_num [chainParams,terminals,helperBound,helperBoundOf,Formula.isLeaf]
  | and p q hp hq => exact step false t p q hp hq
  | or p q hp hq => exact step true t p q hp hq

private lemma coord_uncons_cons (d : Bool) (j : Coord) : (j.cons d).uncons = some (d,j) := by cases j <;> rfl

lemma chain_supported (t : TieRule) (T : Formula m) (k : Coord)
    (hk : k ∉ terminalKeys t T) : chainU t T k = 0 := by
  have gate (g : Bool) (t : TieRule) (p q : Formula m)
      (hp : ∀ t k, k ∉ terminalKeys t p → chainU t p k = 0)
      (hq : ∀ t k, k ∉ terminalKeys t q → chainU t q k = 0)
      (k : Coord) (hk : k ∉ terminalKeys t (mkGate g p q)) :
      chainU t (mkGate g p q) k = 0 := by
    let d := heavyDir t p q
    have keys : terminalKeys t (mkGate g p q) =
        insert ((exportKey (pick (!d) p q)).cons (!d))
          ((terminalKeys (t.sub d) (pick d p q)).image (Coord.cons d)) := by
      cases hd : heavyDir t p q <;> cases g <;> simp [mkGate,terminalKeys,d,hd,pick]
    have ue : chainU t (mkGate g p q) =
        (nodeAngle g t p q (chainParams (t.sub false) p) (chainParams (t.sub true) q)).1 •
          liftV d (chainU (t.sub d) (pick d p q)) +
        (nodeAngle g t p q (chainParams (t.sub false) p) (chainParams (t.sub true) q)).2 •
          liftV (!d) (exportV (pick (!d) p q)) := by
      cases hd : heavyDir t p q <;> cases g <;> simp [mkGate,chainU,uStep,d,hd,pick]
    have hrec (j : Coord) : j ∉ terminalKeys (t.sub d) (pick d p q) →
        chainU (t.sub d) (pick d p q) j = 0 := by
      cases hh : d
      · exact hp _ _
      · exact hq _ _
    rw [keys] at hk
    have go (e : Bool) (j : Coord)
        (hn : j.cons e ∉ insert ((exportKey (pick (!d) p q)).cons (!d))
            ((terminalKeys (t.sub d) (pick d p q)).image (Coord.cons d))) :
        chainU t (mkGate g p q) (j.cons e) = 0 := by
      rw [ue]
      have hz : e = d → chainU (t.sub d) (pick d p q) j = 0 := by
        intro h; subst e
        apply hrec
        exact fun hj => hn (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))
      have hs : e = !d → exportV (pick (!d) p q) j = 0 := by
        intro h; subst e
        have h' : j ≠ exportKey (pick (!d) p q) := by
          rintro rfl; exact hn (Finset.mem_insert_self _ _)
        simp [exportV,basisV,h']
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,liftV,coord_uncons_cons]
      split_ifs <;> simp_all
    cases k with
    | leaf ks =>
      cases ks with
      | nil => simp [ue,liftV,Coord.uncons]
      | cons e p => exact go e (.leaf p) hk
    | helper ks =>
      cases ks with
      | nil => simp [ue,liftV,Coord.uncons]
      | cons e p => exact go e (.helper p) hk
  induction T generalizing t k with
  | lit i b =>
    have h : k ≠ .leaf [] := by simpa [terminalKeys] using hk
    simpa [chainU,basisV,h]
  | and p q hp hq => exact gate false t p q hp hq k hk
  | or p q hp hq => exact gate true t p q hp hq k hk


end ChainTail

theorem solution {m : ℕ} (tie : TieRule) (T : Formula m) (hT : T.isLeaf = false)
    (hterm : ∀ t ∈ terminals tie T,
      (program t.1 t.2).IsVectorForm ∧ (program t.1 t.2).Computes t.2.eval ∧
        (program t.1 t.2).HasBalancedBound (helperBound t.1 t.2)) :
    (chainProgram tie T).Computes T.eval ∧
      (chainProgram tie T).IsVectorForm ∧
      (chainProgram tie T).HasWitnessParams (chainParams tie T).1 (chainParams tie T).2 ∧
      ((chainParams tie T).1 + 1) * (chainParams tie T).2 =
        ((terminals tie T).map (fun t => helperBound t.1 t.2 ^ 2 + helperBound t.1 t.2)).sum ∧
      (∀ k, 0 ≤ chainU tie T k) ∧
      (∀ k, k ∉ terminalKeys tie T → chainU tie T k = 0) := by
  obtain ⟨hv,hc,hw⟩ := ChainReindex.chainSemantics tie T hterm
  exact ⟨hc,hv,hw,ChainTail.chain_product tie T,ChainTail.chain_nonneg tie T,ChainTail.chain_supported tie T⟩
