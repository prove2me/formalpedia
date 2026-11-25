-- Prove2me | solution 1 for DeMorganApprox.Main.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:16:24.184959+00:00
-- url     : https://prove2.me/submissions/9b645d77-640a-4dd5-abce-0ead070be616

import Definitions.Def_DeMorganApprox_Main_GateComposition

open DeMorganApprox.Main DeMorganApprox.Main.SpanProgram

namespace GateProof

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

variable (P : SpanProgram m I₁ J₁) (Q : SpanProgram m I₂ J₂) (x : Fin m → Bool)
theorem avail_and (B D : ℝ) (a : J₁ → ℝ) (b : J₂ → ℝ) :
    (P.andCompose Q B D).applyAvail x (Sum.elim a b) =
      Sum.elim (P.applyAvail x a) (Q.applyAvail x b) := by
  ext i; cases i <;> simp [applyAvail, andCompose, Fintype.sum_sum_type] <;> rfl
theorem avail_or (A C : ℝ) (a : J₁ → ℝ) (b : J₂ → ℝ) (t : ℝ) :
    (P.orCompose Q A C).applyAvail x (Sum.elim (Sum.elim a b) (fun _ => t)) =
      Sum.elim (P.applyAvail x a + (t*(orAngle A C).2) • P.target)
        (Q.applyAvail x b - (t*(orAngle A C).1) • Q.target) := by
  ext i; cases i <;> simp [applyAvail, orCompose, Fintype.sum_sum_type, Label.avail, mul_assoc, sub_eq_add_neg] <;> rfl
end GateProof

namespace GateProof

variable {m : ℕ} {I₁ I₂ J₁ J₂ : Type} [Fintype I₁] [Fintype I₂] [Fintype J₁] [Fintype J₂]

theorem or_case (P : SpanProgram m I₁ J₁) (Q : SpanProgram m I₂ J₂)
    (f g : (Fin m → Bool) → Bool) (A B C D : ℝ)
    (vp : P.IsVectorForm) (vq : Q.IsVectorForm) (cp : P.Computes f) (cq : Q.Computes g)
    (wp : P.HasWitnessParams A B) (wq : Q.HasWitnessParams C D) :
    (P.orCompose Q A C).Computes (fun x => f x || g x) ∧
    (P.orCompose Q A C).HasWitnessParams (orParams A B C D).1 (orParams A B C D).2 ∧
    (P.orCompose Q A C).IsVectorForm ∧
    ((orParams A B C D).1+1)*(orParams A B C D).2 = (A+1)*B + (C+1)*D := by
  classical
  let c := (orAngle A C).1
  let s := (orAngle A C).2
  have ha := wp.1
  have hb := wp.2.1
  have hc := wq.1
  have hd := wq.2.1
  have hp : 0 < A+C+2 := by linarith
  have hu : 0 < (A+1)/(A+C+2) := div_pos (by linarith) hp
  have hv : 0 < (C+1)/(A+C+2) := div_pos (by linarith) hp
  have hcp : 0 < c := Real.sqrt_pos.2 hu
  have hsp : 0 < s := Real.sqrt_pos.2 hv
  have hc2 : c^2 = (A+1)/(A+C+2) := Real.sq_sqrt hu.le
  have hs2 : s^2 = (C+1)/(A+C+2) := Real.sq_sqrt hv.le
  have hcs : c^2+s^2 = 1 := by rw [hc2,hs2]; field_simp; ring
  have hAc : c^2*(A+C+2) = A+1 := (eq_div_iff hp.ne').mp hc2
  have hCs : s^2*(A+C+2) = C+1 := (eq_div_iff hp.ne').mp hs2
  have hnorm : (P.orCompose Q A C).IsVectorForm := by
    constructor
    · change sqNorm (Sum.elim (c • P.target) (s • Q.target)) = 1
      simp [norm_sum, norm_scale, vp.1, vq.1, hcs]
    · rintro ((j|j)|u)
      · change sqNorm (Sum.elim (P.vec j) (0 : I₂ → ℝ)) = 1
        simp [norm_sum,vp.2]
      · change sqNorm (Sum.elim (0 : I₁ → ℝ) (Q.vec j)) = 1
        simp [norm_sum,vq.2]
      · change sqNorm (Sum.elim (s • P.target) (-(c • Q.target))) = 1
        rw [show -(c • Q.target) = (-c) • Q.target by simp]
        rw [norm_sum,norm_scale,norm_scale,vp.1,vq.1]; nlinarith
  have hB : (orParams A B C D).2 = c^2*B + s^2*D := by rw [hc2,hs2]; rfl
  have hT : 1 ≤ (orParams A B C D).2 := by
    rw [hB]; nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hb),
      mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hd)]
  have hres := assemble (P.orCompose Q A C) (fun x => f x || g x)
    (A := (orParams A B C D).1) (by change 1 ≤ A+C+1; linarith) hT
  have hpos (x) (hx : (f x || g x) = true) :
      ∃ a, (P.orCompose Q A C).IsOneWitness x a ∧ sqNorm a ≤ (orParams A B C D).1 := by
    rcases Bool.or_eq_true_iff.mp hx with hx|hx
    · obtain ⟨a,hw,hn⟩ := (wp.2.2 x).1 ((cp x).mpr hx)
      refine ⟨Sum.elim (Sum.elim (c⁻¹ • a) (0 : J₂ → ℝ)) (fun _ => -s/c), ?_, ?_⟩
      · unfold IsOneWitness at hw ⊢
        rw [avail_or,avail_scale,hw,avail_zero]
        change Sum.elim (c⁻¹ • P.target + (-s/c*s) • P.target)
          (0 - (-s/c*c) • Q.target) = Sum.elim (c • P.target) (s • Q.target)
        ext i; cases i with
        | inl i => simp [hcp.ne',hsp.ne']; field_simp [hcp.ne',hsp.ne']; linear_combination -(P.target i) * hcs
        | inr i => simp [hcp.ne',hsp.ne']
      · change _ ≤ A+C+1
        rw [norm_sum,norm_sum,norm_scale,norm_zero]
        simp only [sqNorm, Fintype.sum_unique, add_zero] at *
        have hl := mul_le_mul_of_nonneg_left hn (sq_nonneg c⁻¹)
        calc
          _ ≤ c⁻¹ ^ 2 * A + (-s / c)^2 := by linarith
          _ = A+C+1 := by field_simp; nlinarith [hcs,hAc]
    · obtain ⟨a,hw,hn⟩ := (wq.2.2 x).1 ((cq x).mpr hx)
      refine ⟨Sum.elim (Sum.elim (0 : J₁ → ℝ) (s⁻¹ • a)) (fun _ => c/s), ?_, ?_⟩
      · unfold IsOneWitness at hw ⊢
        rw [avail_or,avail_scale,hw,avail_zero]
        change Sum.elim (0 + (c/s*s) • P.target)
          (s⁻¹ • Q.target - (c/s*c) • Q.target) = Sum.elim (c • P.target) (s • Q.target)
        ext i; cases i with
        | inl i => simp [hsp.ne']
        | inr i => simp [hsp.ne']; field_simp [hsp.ne']; linear_combination -(Q.target i) * hcs
      · change _ ≤ A+C+1
        rw [norm_sum,norm_sum,norm_scale,norm_zero]
        simp only [sqNorm, Fintype.sum_unique, zero_add] at *
        have hl := mul_le_mul_of_nonneg_left hn (sq_nonneg s⁻¹)
        calc
          _ ≤ s⁻¹ ^ 2 * C + (c / s)^2 := by linarith
          _ = A+C+1 := by field_simp; nlinarith [hcs,hCs]
  have hneg (x) (hx : (f x || g x) = false) :
      ∃ w, (P.orCompose Q A C).IsZeroWitness x w ∧ sqNorm w ≤ (orParams A B C D).2 := by
    simp only [Bool.or_eq_false_iff] at hx
    obtain ⟨w,hw,hn⟩ := (wp.2.2 x).2 (fun h => by simpa [hx.1] using (cp x).mp h)
    obtain ⟨v,hv,hm⟩ := (wq.2.2 x).2 (fun h => by simpa [hx.2] using (cq x).mp h)
    refine ⟨Sum.elim (c • w) (s • v), ⟨?_,?_⟩,?_⟩
    · change pair (Sum.elim (c • w) (s • v)) (Sum.elim (c • P.target) (s • Q.target)) = 1
      rw [pair_sum,pair_scale,pair_scale,show pair w P.target = 1 from hw.1,show pair v Q.target = 1 from hv.1]; nlinarith
    · rintro ((j|j)|u) hj
      · change pair (Sum.elim (c • w) (s • v)) (Sum.elim (P.vec j) 0) = 0
        rw [pair_sum,← one_smul ℝ (P.vec j),pair_scale,show pair w (P.vec j) = 0 from hw.2 j hj]; simp
      · change pair (Sum.elim (c • w) (s • v)) (Sum.elim 0 (Q.vec j)) = 0
        rw [pair_sum,← one_smul ℝ (Q.vec j),pair_scale,show pair v (Q.vec j) = 0 from hv.2 j hj]; simp
      · change pair (Sum.elim (c • w) (s • v)) (Sum.elim (s • P.target) (-(c • Q.target))) = 0
        rw [show -(c • Q.target) = (-c) • Q.target by simp,pair_sum,pair_scale,pair_scale,show pair w P.target = 1 from hw.1,show pair v Q.target = 1 from hv.1]; ring
    · rw [norm_sum,norm_scale,norm_scale,hB]
      exact add_le_add (mul_le_mul_of_nonneg_left hn (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hm (sq_nonneg _))
  obtain ⟨hc',hw'⟩ := hres hpos hneg
  refine ⟨hc',hw',hnorm,?_⟩
  dsimp [orParams]; field_simp; ring
end GateProof

namespace GateProof
variable {m : ℕ} {I₁ I₂ J₁ J₂ : Type} [Fintype I₁] [Fintype I₂] [Fintype J₁] [Fintype J₂]
theorem and_case (P : SpanProgram m I₁ J₁) (Q : SpanProgram m I₂ J₂)
    (f g : (Fin m → Bool) → Bool) (A B C D : ℝ)
    (vp : P.IsVectorForm) (vq : Q.IsVectorForm) (cp : P.Computes f) (cq : Q.Computes g)
    (wp : P.HasWitnessParams A B) (wq : Q.HasWitnessParams C D) :
    (P.andCompose Q B D).Computes (fun x => f x && g x) ∧
    (P.andCompose Q B D).HasWitnessParams (andParams A B C D).1 (andParams A B C D).2 ∧
    (P.andCompose Q B D).IsVectorForm ∧
    ((andParams A B C D).1+1)*(andParams A B C D).2 = (A+1)*B + (C+1)*D := by
  classical
  let c := (andAngle B D).1
  let s := (andAngle B D).2
  have ha := wp.1
  have hb := wp.2.1
  have hc := wq.1
  have hd := wq.2.1
  have hp : 0 < B+D := by linarith
  have hu : 0 < B/(B+D) := div_pos (by linarith) hp
  have hv : 0 < D/(B+D) := div_pos (by linarith) hp
  have hcp : 0 < c := Real.sqrt_pos.2 hu
  have hsp : 0 < s := Real.sqrt_pos.2 hv
  have hc2 : c^2 = B/(B+D) := Real.sq_sqrt hu.le
  have hs2 : s^2 = D/(B+D) := Real.sq_sqrt hv.le
  have hcs : c^2+s^2 = 1 := by rw [hc2,hs2]; field_simp
  have hAc : c^2*(B+D) = B := (eq_div_iff hp.ne').mp hc2
  have hCs : s^2*(B+D) = D := (eq_div_iff hp.ne').mp hs2
  have hnorm : (P.andCompose Q B D).IsVectorForm := by
    constructor
    · change sqNorm (Sum.elim (c • P.target) (s • Q.target)) = 1
      simp [norm_sum, norm_scale, vp.1, vq.1, hcs]
    · rintro (j|j)
      · change sqNorm (Sum.elim (P.vec j) (0 : I₂ → ℝ)) = 1
        simp [norm_sum,vp.2]
      · change sqNorm (Sum.elim (0 : I₁ → ℝ) (Q.vec j)) = 1
        simp [norm_sum,vq.2]
  have hA : (andParams A B C D).1 = c^2*A + s^2*C := by rw [hc2,hs2]; rfl
  have hT : 1 ≤ (andParams A B C D).1 := by
    rw [hA]; nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr ha),
      mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hc)]
  have hres := assemble (P.andCompose Q B D) (fun x => f x && g x) hT
    (B := (andParams A B C D).2) (by change 1 ≤ B+D; linarith)
  have hpos (x) (hx : (f x && g x) = true) :
      ∃ a, (P.andCompose Q B D).IsOneWitness x a ∧ sqNorm a ≤ (andParams A B C D).1 := by
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp hx
    obtain ⟨a,hw,hn⟩ := (wp.2.2 x).1 ((cp x).mpr h1)
    obtain ⟨b,hv,hm⟩ := (wq.2.2 x).1 ((cq x).mpr h2)
    refine ⟨Sum.elim (c • a) (s • b),?_,?_⟩
    · unfold IsOneWitness at hw hv ⊢
      rw [avail_and, avail_scale,avail_scale,hw,hv]; rfl
    · rw [norm_sum,norm_scale,norm_scale,hA]
      exact add_le_add (mul_le_mul_of_nonneg_left hn (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hm (sq_nonneg _))
  have hneg (x) (hx : (f x && g x) = false) :
      ∃ w, (P.andCompose Q B D).IsZeroWitness x w ∧ sqNorm w ≤ (andParams A B C D).2 := by
    rcases Bool.and_eq_false_iff.mp hx with hx|hx
    · obtain ⟨w,hw,hn⟩ := (wp.2.2 x).2 (fun h => by simpa [hx] using (cp x).mp h)
      refine ⟨Sum.elim (c⁻¹ • w) (0 : I₂ → ℝ), ⟨?_,?_⟩,?_⟩
      · change pair (Sum.elim (c⁻¹ • w) (0 : I₂ → ℝ)) (Sum.elim (c • P.target) (s • Q.target)) = 1
        rw [pair_sum,pair_scale,show pair w P.target = 1 from hw.1]
        simp [hcp.ne']
      · rintro (j|j) hj
        · change pair (Sum.elim (c⁻¹ • w) (0 : I₂ → ℝ)) (Sum.elim (P.vec j) 0) = 0
          rw [pair_sum,← one_smul ℝ (P.vec j),pair_scale,show pair w (P.vec j) = 0 from hw.2 j hj]; simp
        · change pair (Sum.elim (c⁻¹ • w) (0 : I₂ → ℝ)) (Sum.elim 0 (Q.vec j)) = 0
          simp [pair_sum]
      · rw [norm_sum,norm_zero,norm_scale,add_zero]
        calc
          _ ≤ c⁻¹ ^ 2 * B := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
          _ = B+D := by field_simp [hcp.ne']; nlinarith only [hAc]
    · obtain ⟨v,hv,hm⟩ := (wq.2.2 x).2 (fun h => by simpa [hx] using (cq x).mp h)
      refine ⟨Sum.elim (0 : I₁ → ℝ) (s⁻¹ • v), ⟨?_,?_⟩,?_⟩
      · change pair (Sum.elim (0 : I₁ → ℝ) (s⁻¹ • v)) (Sum.elim (c • P.target) (s • Q.target)) = 1
        rw [pair_sum,pair_scale,show pair v Q.target = 1 from hv.1]
        simp [hsp.ne']
      · rintro (j|j) hj
        · change pair (Sum.elim (0 : I₁ → ℝ) (s⁻¹ • v)) (Sum.elim (P.vec j) 0) = 0
          simp [pair_sum]
        · change pair (Sum.elim (0 : I₁ → ℝ) (s⁻¹ • v)) (Sum.elim 0 (Q.vec j)) = 0
          rw [pair_sum,← one_smul ℝ (Q.vec j),pair_scale,show pair v (Q.vec j) = 0 from hv.2 j hj]; simp
      · rw [norm_sum,norm_zero,norm_scale,zero_add]
        calc
          _ ≤ s⁻¹ ^ 2 * D := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
          _ = B+D := by field_simp [hsp.ne']; nlinarith only [hCs]
  obtain ⟨hc',hw'⟩ := hres hpos hneg
  refine ⟨hc',hw',hnorm,?_⟩
  dsimp [andParams]; field_simp; ring
end GateProof

theorem solution {m : ℕ} {ι₁ ι₂ J₁ J₂ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype J₁]
    [Fintype J₂] (P₁ : SpanProgram m ι₁ J₁) (P₂ : SpanProgram m ι₂ J₂)
    (f₁ f₂ : (Fin m → Bool) → Bool) (A₁ B₁ A₂ B₂ : ℝ)
    (hv₁ : P₁.IsVectorForm) (hv₂ : P₂.IsVectorForm)
    (hc₁ : P₁.Computes f₁) (hc₂ : P₂.Computes f₂)
    (hw₁ : P₁.HasWitnessParams A₁ B₁) (hw₂ : P₂.HasWitnessParams A₂ B₂) :
    -- OR gate
    ((P₁.orCompose P₂ A₁ A₂).Computes (fun x => f₁ x || f₂ x) ∧
      (P₁.orCompose P₂ A₁ A₂).IsVectorForm ∧
      (∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧
        (P₁.orCompose P₂ A₁ A₂).target = Sum.elim (c • P₁.target) (s • P₂.target)) ∧
      (∀ j, (P₁.orCompose P₂ A₁ A₂).vec (.inl (.inl j)) = Sum.elim (P₁.vec j) (0 : ι₂ → ℝ) ∧
        (P₁.orCompose P₂ A₁ A₂).label (.inl (.inl j)) = P₁.label j) ∧
      (∀ j, (P₁.orCompose P₂ A₁ A₂).vec (.inl (.inr j)) = Sum.elim (0 : ι₁ → ℝ) (P₂.vec j) ∧
        (P₁.orCompose P₂ A₁ A₂).label (.inl (.inr j)) = P₂.label j) ∧
      (P₁.orCompose P₂ A₁ A₂).label (.inr ()) = Label.always ∧
      (P₁.orCompose P₂ A₁ A₂).HasWitnessParams
        (orParams A₁ B₁ A₂ B₂).1 (orParams A₁ B₁ A₂ B₂).2 ∧
      ((orParams A₁ B₁ A₂ B₂).1 + 1) * (orParams A₁ B₁ A₂ B₂).2 =
        (A₁ + 1) * B₁ + (A₂ + 1) * B₂) ∧
    -- AND gate
    ((P₁.andCompose P₂ B₁ B₂).Computes (fun x => f₁ x && f₂ x) ∧
      (P₁.andCompose P₂ B₁ B₂).IsVectorForm ∧
      (∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧
        (P₁.andCompose P₂ B₁ B₂).target = Sum.elim (c • P₁.target) (s • P₂.target)) ∧
      (∀ j, (P₁.andCompose P₂ B₁ B₂).vec (.inl j) = Sum.elim (P₁.vec j) (0 : ι₂ → ℝ) ∧
        (P₁.andCompose P₂ B₁ B₂).label (.inl j) = P₁.label j) ∧
      (∀ j, (P₁.andCompose P₂ B₁ B₂).vec (.inr j) = Sum.elim (0 : ι₁ → ℝ) (P₂.vec j) ∧
        (P₁.andCompose P₂ B₁ B₂).label (.inr j) = P₂.label j) ∧
      (P₁.andCompose P₂ B₁ B₂).HasWitnessParams
        (andParams A₁ B₁ A₂ B₂).1 (andParams A₁ B₁ A₂ B₂).2 ∧
      ((andParams A₁ B₁ A₂ B₂).1 + 1) * (andParams A₁ B₁ A₂ B₂).2 =
        (A₁ + 1) * B₁ + (A₂ + 1) * B₂) := by
  obtain ⟨oc,ow,ov,oi⟩ := GateProof.or_case P₁ P₂ f₁ f₂ A₁ B₁ A₂ B₂ hv₁ hv₂ hc₁ hc₂ hw₁ hw₂
  obtain ⟨ac,aw,av,ai⟩ := GateProof.and_case P₁ P₂ f₁ f₂ A₁ B₁ A₂ B₂ hv₁ hv₂ hc₁ hc₂ hw₁ hw₂
  exact ⟨⟨oc,ov,⟨_,_,Real.sqrt_nonneg _,Real.sqrt_nonneg _,rfl⟩,fun _ => ⟨rfl,rfl⟩,
    fun _ => ⟨rfl,rfl⟩, rfl,ow,oi⟩, ⟨ac,av,⟨_,_,Real.sqrt_nonneg _,Real.sqrt_nonneg _,rfl⟩,
    fun _ => ⟨rfl,rfl⟩,fun _ => ⟨rfl,rfl⟩,aw,ai⟩⟩
