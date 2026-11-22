-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:27:08.149834+00:00
-- url     : https://prove2.me/submissions/68ac59c0-ef11-4fb1-aa82-b2cb530d1cca

import Definitions.Def_GL2QFT_Supplement_Mackey

noncomputable section

open Classical
open scoped Matrix ComplexConjugate
open GL2QFT GL2QFT.Induction GL2QFT.Supplement GL2QFT.Supplement.Mackey

namespace GL2QFT.Supplement.MackeyProof

/-! ### Part 1: Unitary representations, Schur's lemma, Schur orthogonality, Peter–Weyl completeness,
and unitarity of `UIndLam` -/

private theorem isUnitaryRep_mul_conjTranspose {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g * (R g)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hR.2 g)

private theorem isUnitaryRep_conjTranspose_mul {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    (R g)ᴴ * R g = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hR.2 g)

private theorem isUnitaryRep_inv_eq_conjTranspose {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g⁻¹ = (R g)ᴴ := by
  have h1 : R g * R g⁻¹ = 1 := by
    rw [← hR.1.2, mul_inv_cancel, hR.1.1]
  have h2 : (R g)ᴴ * R g = 1 := isUnitaryRep_conjTranspose_mul hR g
  calc R g⁻¹ = 1 * R g⁻¹ := (Matrix.one_mul _).symm
    _ = ((R g)ᴴ * R g) * R g⁻¹ := by rw [h2]
    _ = (R g)ᴴ * (R g * R g⁻¹) := Matrix.mul_assoc _ _ _
    _ = (R g)ᴴ := by rw [h1, Matrix.mul_one]

private theorem ker_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₁ (LinearMap.ker A.mulVecLin) := by
  intro g v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hA g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

private theorem range_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₂ (LinearMap.range A.mulVecLin) := by
  intro g w hw
  rcases hw with ⟨v, rfl⟩
  refine ⟨R₁ g *ᵥ v, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hA g, ← Matrix.mulVec_mulVec]
  rfl

private theorem mulVecLin_eq_zero_iff {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Matrix ι₂ ι₁ ℂ) : (∀ v, A *ᵥ v = 0) ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have := congr_fun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  · intro h v
    subst h
    simp

private theorem schur_zero_of_not_repEquiv {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (hi1 : IsIrreducibleRep R₁) (hi2 : IsIrreducibleRep R₂)
    (hne : ¬ RepEquiv R₁ R₂) {A : Matrix ι₂ ι₁ ℂ}
    (hA : ∀ g : G, R₂ g * A = A * R₁ g) : A = 0 := by
  by_contra hAne
  have hker_ne : LinearMap.ker A.mulVecLin ≠ ⊤ := by
    intro htop
    apply hAne
    rw [← mulVecLin_eq_zero_iff]
    intro v
    have hv : v ∈ LinearMap.ker A.mulVecLin := htop.symm ▸ Submodule.mem_top
    simpa [Matrix.mulVecLin_apply] using hv
  have hker : LinearMap.ker A.mulVecLin = ⊥ :=
    (hi1.2 _ (ker_invariant hA)).resolve_right hker_ne
  have hinj : Function.Injective A.mulVecLin := LinearMap.ker_eq_bot.mp hker
  have hrange_ne : LinearMap.range A.mulVecLin ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [← mulVecLin_eq_zero_iff]
    intro v
    have hv : A.mulVecLin v ∈ (⊥ : Submodule ℂ (ι₂ → ℂ)) := hbot ▸ LinearMap.mem_range_self _ v
    simpa [Matrix.mulVecLin_apply] using hv
  have hrange : LinearMap.range A.mulVecLin = ⊤ :=
    (hi2.2 _ (range_invariant hA)).resolve_left hrange_ne
  have hsurj : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.mp hrange
  let e : (ι₁ → ℂ) ≃ₗ[ℂ] (ι₂ → ℂ) := LinearEquiv.ofBijective A.mulVecLin ⟨hinj, hsurj⟩
  let B : Matrix ι₁ ι₂ ℂ := LinearMap.toMatrix' e.symm.toLinearMap
  have hA_eq : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
  have hAB : A * B = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp]
    have hc : A.mulVecLin.comp e.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun v => e.apply_symm_apply v
    rw [hc, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp]
    have hc : e.symm.toLinearMap.comp A.mulVecLin = LinearMap.id :=
      LinearMap.ext fun v => e.symm_apply_apply v
    rw [hc, LinearMap.toMatrix'_id]
  exact hne ⟨A, B, hAB, hBA, fun g _ => (hA g).symm⟩

private theorem schur_eq_smul_one {G ι : Type} [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hi : IsIrreducibleRep R)
    {A : Matrix ι ι ℂ} (hA : ∀ g : G, R g * A = A * R g) :
    ∃ c : ℂ, A = c • (1 : Matrix ι ι ℂ) := by
  have : Nonempty ι := hi.1
  have : Nontrivial (ι → ℂ) := Function.nontrivial
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A.mulVecLin
  have hker_ne : LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin ≠ ⊥ := by
    rw [Module.End.hasEigenvalue_iff] at hc
    intro hbot
    apply hc
    rw [Submodule.eq_bot_iff] at hbot ⊢
    intro v hv
    apply hbot
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa [Matrix.mulVecLin_apply, sub_eq_zero] using hv
  have hA' : ∀ g : G, R g * (A - c • (1 : Matrix ι ι ℂ)) =
      (A - c • (1 : Matrix ι ι ℂ)) * R g := by
    intro g
    simp [mul_sub, sub_mul, hA g]
  have hker_top : LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin = ⊤ :=
    (hi.2 _ (ker_invariant hA')).resolve_left hker_ne
  refine ⟨c, ?_⟩
  rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
  intro v
  have hv : v ∈ LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin := hker_top.symm ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  exact hv

private theorem schur_orthogonality_ne {K ι₁ ι₂ : Type} [Group K] [Fintype K]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : K → Matrix ι₁ ι₁ ℂ} {R₂ : K → Matrix ι₂ ι₂ ℂ}
    (h1 : IsUnitaryRep R₁) (h2 : IsUnitaryRep R₂)
    (hi1 : IsIrreducibleRep R₁) (hi2 : IsIrreducibleRep R₂)
    (hne : ¬ RepEquiv R₁ R₂) (i j : ι₂) (i' j' : ι₁) :
    ∑ g : K, R₂ g i j * star (R₁ g i' j') = 0 := by
  let M : Matrix ι₂ ι₁ ℂ := Matrix.single j j' 1
  let A : Matrix ι₂ ι₁ ℂ := ∑ g : K, R₂ g * M * R₁ g⁻¹
  have hA : ∀ x : K, R₂ x * A = A * R₁ x := by
    intro x
    calc R₂ x * A
        = ∑ g : K, R₂ x * (R₂ g * M * R₁ g⁻¹) := by dsimp [A]; rw [Matrix.mul_sum]
      _ = ∑ g : K, R₂ (x * g) * M * R₁ g⁻¹ := by
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [Matrix.mul_assoc, h2.1.2]
      _ = ∑ h : K, R₂ h * M * R₁ (x⁻¹ * h)⁻¹ := by
          refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun g => ?_
          simp
      _ = ∑ h : K, (R₂ h * M * R₁ h⁻¹) * R₁ x := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [mul_inv_rev, inv_inv, h1.1.2]
          simp only [Matrix.mul_assoc]
      _ = A * R₁ x := by dsimp [A]; rw [Matrix.sum_mul]
  have hA0 : A = 0 := schur_zero_of_not_repEquiv hi1 hi2 hne hA
  have hAentry : A i i' = ∑ g : K, R₂ g i j * star (R₁ g i' j') := by
    simp only [A, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [isUnitaryRep_inv_eq_conjTranspose h1 g, Matrix.mul_apply]
    have hmul : ∀ k, (R₂ g * M) i k = if k = j' then R₂ g i j else 0 := by
      intro k
      simp only [M, Matrix.mul_apply, Matrix.single_apply]
      rw [Finset.sum_eq_single j]
      · by_cases hk : k = j' <;> simp [hk, Ne.symm]
      · intro a _ ha
        simp [ha.symm]
      · intro hj
        exact False.elim (hj (Finset.mem_univ _))
    simp [hmul, Matrix.conjTranspose_apply]
  rw [← hAentry, hA0, Matrix.zero_apply]

private theorem schur_orthogonality_eq {K ι : Type} [Group K] [Fintype K]
    [Fintype ι] [DecidableEq ι]
    {R : K → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (hi : IsIrreducibleRep R)
    (i j i' j' : ι) :
    ∑ g : K, R g i j * star (R g i' j') =
      ((Fintype.card K : ℂ) / (Fintype.card ι : ℂ)) *
        (if i = i' then 1 else 0) * (if j = j' then 1 else 0) := by
  let M : Matrix ι ι ℂ := Matrix.single j j' 1
  let A : Matrix ι ι ℂ := ∑ g : K, R g * M * R g⁻¹
  have hA : ∀ x : K, R x * A = A * R x := by
    intro x
    calc R x * A
        = ∑ g : K, R x * (R g * M * R g⁻¹) := by dsimp [A]; rw [Matrix.mul_sum]
      _ = ∑ g : K, R (x * g) * M * R g⁻¹ := by
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [Matrix.mul_assoc, hR.1.2]
      _ = ∑ h : K, R h * M * R (x⁻¹ * h)⁻¹ := by
          refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun g => ?_
          simp
      _ = ∑ h : K, (R h * M * R h⁻¹) * R x := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [mul_inv_rev, inv_inv, hR.1.2]
          simp only [Matrix.mul_assoc]
      _ = A * R x := by dsimp [A]; rw [Matrix.sum_mul]
  obtain ⟨c, hc⟩ := schur_eq_smul_one hi hA
  have htr1 : A.trace = c * (Fintype.card ι : ℂ) := by
    rw [hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_comm]
  have htr2 : A.trace = (Fintype.card K : ℂ) * (if j = j' then 1 else 0) := by
    simp only [A, Matrix.trace_sum]
    have hterm : ∀ g : K, (R g * M * R g⁻¹).trace = if j = j' then 1 else 0 := by
      intro g
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← hR.1.2, inv_mul_cancel, hR.1.1,
        Matrix.one_mul]
      simp only [M, Matrix.trace, Matrix.diag, Matrix.single_apply]
      split_ifs with hjj
      · subst hjj
        rw [Finset.sum_eq_single j]
        · simp
        · intro a _ ha; simp [ha.symm]
        · intro hj; exact False.elim (hj (Finset.mem_univ _))
      · simp [Ne.symm hjj]
    simp [hterm]
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by
    have : Nonempty ι := hi.1
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc_val : c = ((Fintype.card K : ℂ) / (Fintype.card ι : ℂ)) * (if j = j' then 1 else 0) := by
    have hceq : c * (Fintype.card ι : ℂ) = (Fintype.card K : ℂ) * (if j = j' then 1 else 0) :=
      htr1.symm.trans htr2
    have : c = (c * (Fintype.card ι : ℂ)) / (Fintype.card ι : ℂ) := by
      rw [mul_div_cancel_right₀ _ hd]
    rw [this, hceq, mul_div_right_comm]
  have hAentry : A i i' = ∑ g : K, R g i j * star (R g i' j') := by
    simp only [A, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [isUnitaryRep_inv_eq_conjTranspose hR g, Matrix.mul_apply]
    have hmul : ∀ k, (R g * M) i k = if k = j' then R g i j else 0 := by
      intro k
      simp only [M, Matrix.mul_apply, Matrix.single_apply]
      rw [Finset.sum_eq_single j]
      · by_cases hk : k = j' <;> simp [hk, Ne.symm]
      · intro a _ ha; simp [ha.symm]
      · intro hj; exact False.elim (hj (Finset.mem_univ _))
    simp [hmul, Matrix.conjTranspose_apply]
  rw [← hAentry, hc, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hc_val]
  split_ifs <;> ring

private theorem fourierMatrix_mul_conjTranspose {K Λ : Type} [Group K] [Fintype K]
    [Fintype Λ] {B : Λ → Type} [∀ μ, Fintype (B μ)] [∀ μ, DecidableEq (B μ)]
    {R : ∀ μ, K → Matrix (B μ) (B μ) ℂ} (hR : IsIrrepSystem R) :
    fourierMatrix R * (fourierMatrix R)ᴴ = 1 := by
  ext ⟨μ, i, j⟩ ⟨μ', i', j'⟩
  simp only [Matrix.mul_apply, fourierMatrix, Matrix.of_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply]
  have hpull :
      ∑ g : K, ((Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ) * R μ g i j) *
        star ((Real.sqrt ((Fintype.card (B μ') : ℝ) / (Fintype.card K : ℝ)) : ℂ) * R μ' g i' j') =
      (Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ) *
        (Real.sqrt ((Fintype.card (B μ') : ℝ) / (Fintype.card K : ℝ)) : ℂ) *
        ∑ g : K, R μ g i j * star (R μ' g i' j') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hpull]
  by_cases hμ : μ = μ'
  · subst hμ
    rw [schur_orthogonality_eq (hR.1 μ) (hR.2.1 μ) i j i' j']
    have : Nonempty (B μ) := (hR.2.1 μ).1
    have hd_pos : (0 : ℝ) < Fintype.card (B μ) := Nat.cast_pos.mpr Fintype.card_pos
    have hK_pos : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
    have hsq :
        (Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ) *
          (Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ) =
          ((Fintype.card (B μ) : ℂ) / (Fintype.card K : ℂ)) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_div,
        Complex.ofReal_natCast, Complex.ofReal_natCast]
    rw [hsq]
    have hd_ne : (Fintype.card (B μ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hK_ne : (Fintype.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    by_cases hi : i = i' <;> by_cases hj : j = j'
    · subst hi; subst hj
      simp [hd_ne, hK_ne]
    · simp [hi, hj]
    · simp [hi, hj]
    · simp [hi, hj]
  · rw [schur_orthogonality_ne (hR.1 μ') (hR.1 μ) (hR.2.1 μ') (hR.2.1 μ)
      (hR.2.2.1 μ' μ (Ne.symm hμ)) i j i' j']
    simp [hμ]

private theorem fourierMatrix_conjTranspose_mul {K Λ : Type} [Group K] [Fintype K]
    [Fintype Λ] {B : Λ → Type} [∀ μ, Fintype (B μ)] [∀ μ, DecidableEq (B μ)]
    {R : ∀ μ, K → Matrix (B μ) (B μ) ℂ} (hR : IsIrrepSystem R) :
    (fourierMatrix R)ᴴ * fourierMatrix R = 1 := by
  let ip : (K → ℂ) → (K → ℂ) → ℂ := fun u v => ∑ g : K, star (u g) * v g
  have hip_self_zero : ∀ u : K → ℂ, ip u u = 0 → u = 0 := by
    intro u hu
    ext g
    have hre : (ip u u).re = 0 := by rw [hu]; simp
    have hsum : ∑ x : K, ((u x).re * (u x).re + (u x).im * (u x).im) = 0 := by
      have hterm_re : ∀ x : K, (star (u x) * u x).re = (u x).re * (u x).re + (u x).im * (u x).im :=
        fun x => by simp [Complex.mul_re]
      simpa [ip, Complex.re_sum, hterm_re] using hre
    have hterm : (u g).re * (u g).re + (u g).im * (u g).im = 0 := by
      have hnn : ∀ x ∈ (Finset.univ : Finset K),
          0 ≤ (u x).re * (u x).re + (u x).im * (u x).im :=
        fun x _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum g (Finset.mem_univ g)
    have hre0 : (u g).re = 0 := by nlinarith
    have him0 : (u g).im = 0 := by nlinarith
    exact Complex.ext hre0 him0
  let φ : (Σ μ, B μ × B μ) → (K → ℂ) := fun a g => star (fourierMatrix R a g)
  have hip_φ : ∀ a b, ip (φ a) (φ b) = if a = b then 1 else 0 := by
    intro a b
    have h1 : ip (φ a) (φ b) = (fourierMatrix R * (fourierMatrix R)ᴴ) a b := by
      simp [ip, φ, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h1, fourierMatrix_mul_conjTranspose hR, Matrix.one_apply]
  let W : Submodule ℂ (K → ℂ) := Submodule.span ℂ (Set.range φ)
  let Wperp : Submodule ℂ (K → ℂ) :=
    { carrier := {u | ∀ v ∈ W, ip v u = 0}
      zero_mem' := fun v _ => by simp [ip]
      add_mem' := fun {u₁ u₂} h₁ h₂ v hv => by
        have : ip v (u₁ + u₂) = ip v u₁ + ip v u₂ := by
          simp [ip, mul_add, Finset.sum_add_distrib]
        rw [this, h₁ v hv, h₂ v hv, add_zero]
      smul_mem' := fun c {u} hu v hv => by
        have : ip v (c • u) = c * ip v u := by
          simp [ip, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_; ring
        rw [this, hu v hv, mul_zero] }
  let L : K → (K → ℂ) →ₗ[ℂ] (K → ℂ) := fun x =>
    { toFun := fun f g => f (x⁻¹ * g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL_one : ∀ u, L 1 u = u := fun u => by ext g; simp [L]
  have hL_mul : ∀ x y u, L (x * y) u = L x (L y u) := fun x y u => by
    ext g; simp [L, mul_assoc]
  have hL_ip : ∀ x u v, ip (L x u) (L x v) = ip u v := by
    intro x u v
    exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ fun g => by simp [L]
  have hL_W : ∀ x, ∀ v ∈ W, L x v ∈ W := by
    intro x v hv
    refine Submodule.span_induction (p := fun v _ => L x v ∈ W) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨μ, i, j⟩, rfl⟩
      have hterm : L x (φ ⟨μ, i, j⟩) = ∑ k : B μ, (R μ x k i) • φ ⟨μ, k, j⟩ := by
        ext g
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, φ, fourierMatrix, Matrix.of_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
          Complex.conj_ofReal]
        have hmat : R μ (x⁻¹ * g) i j = ∑ k : B μ, star (R μ x k i) * R μ g k j := by
          rw [(hR.1 μ).1.2 x⁻¹ g, isUnitaryRep_inv_eq_conjTranspose (hR.1 μ) x, Matrix.mul_apply]
          simp [Matrix.conjTranspose_apply]
        rw [hmat, map_sum]
        simp only [map_mul, Complex.star_def, starRingEnd_self_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hterm]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · simp
    · intro a b _ _ ha hb; rw [map_add]; exact W.add_mem ha hb
    · intro c a _ ha; rw [map_smul]; exact W.smul_mem c ha
  have hL_Wperp : ∀ x, ∀ u ∈ Wperp, L x u ∈ Wperp := by
    intro x u hu v hv
    have hv' : L x⁻¹ v ∈ W := hL_W x⁻¹ v hv
    have heq : L x (L x⁻¹ v) = v := by rw [← hL_mul, mul_inv_cancel, hL_one]
    calc ip v (L x u) = ip (L x (L x⁻¹ v)) (L x u) := by rw [heq]
      _ = ip (L x⁻¹ v) u := hL_ip x (L x⁻¹ v) u
      _ = 0 := hu _ hv'
  have hWperp_bot : Wperp = ⊥ := by
    by_contra hne
    let P : ℕ → Prop := fun n =>
      ∃ U : Submodule ℂ (K → ℂ), U ≤ Wperp ∧ U ≠ ⊥ ∧ (∀ x, ∀ u ∈ U, L x u ∈ U) ∧
        Module.finrank ℂ U = n
    have hex : ∃ n, P n := ⟨Module.finrank ℂ Wperp, Wperp, le_rfl, hne, hL_Wperp, rfl⟩
    let n := Nat.find hex
    obtain ⟨U, hUW, hUne, hUL, hUdim⟩ := Nat.find_spec hex
    have : FiniteDimensional ℂ (K → ℂ) := inferInstance
    have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
    have hn_pos : 0 < n := by
      rw [show n = Module.finrank ℂ U from hUdim.symm]
      exact Module.finrank_pos
    let b : Module.Basis (Fin n) ℂ U := Module.finBasisOfFinrankEq ℂ U hUdim
    let L_U : K → U →ₗ[ℂ] U := fun x =>
      { toFun := fun u => ⟨L x u.1, hUL x u.1 u.2⟩
        map_add' := fun u v => Subtype.ext (map_add (L x) u.1 v.1)
        map_smul' := fun c u => Subtype.ext (map_smul (L x) c u.1) }
    let ρ : K → Matrix (Fin n) (Fin n) ℂ := fun x => LinearMap.toMatrix b b (L_U x)
    have hρ_mat : IsMatRep ρ := by
      constructor
      · have h1 : L_U 1 = LinearMap.id := by
          ext u g; simp [L_U, hL_one]
        simp [ρ, h1]
      · intro x y
        have hm : L_U (x * y) = (L_U x).comp (L_U y) := by
          ext u g; simp [L_U, hL_mul]
        simp [ρ, hm, LinearMap.toMatrix_comp b b b]
    have hρ_irred : IsIrreducibleRep ρ := by
      refine ⟨⟨⟨0, hn_pos⟩⟩, fun V hV => ?_⟩
      let U' : Submodule ℂ U := V.map b.equivFun.symm.toLinearMap
      let U'' : Submodule ℂ (K → ℂ) := U'.map U.subtype
      have hU''_le : U'' ≤ U := Submodule.map_subtype_le U U'
      have hU''_L : ∀ x, ∀ u ∈ U'', L x u ∈ U'' := by
        intro x u hu
        rcases hu with ⟨u', ⟨v, hv, rfl⟩, rfl⟩
        have hLU : L_U x (b.equivFun.symm v) = b.equivFun.symm ((ρ x).mulVec v) := by
          apply b.equivFun.injective
          rw [b.equivFun.apply_symm_apply]
          ext i
          have hmv := congrFun (LinearMap.toMatrix_mulVec_repr b b (L_U x) (b.equivFun.symm v)) i
          rw [Module.Basis.equivFun_apply, ← hmv]
          change ((ρ x).mulVec (fun j => b.repr (b.equivFun.symm v) j)) i = ((ρ x).mulVec v) i
          refine congrArg (fun w => (ρ x).mulVec w i) ?_
          ext j
          rw [← Module.Basis.equivFun_apply, b.equivFun.apply_symm_apply]
        refine ⟨L_U x (b.equivFun.symm v), ⟨(ρ x).mulVec v, hV x v hv, hLU.symm⟩, rfl⟩
      by_cases hbot : U'' = ⊥
      · left
        have hU'_bot : U' = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro x hx
          have : (x : K → ℂ) ∈ U'' := ⟨x, hx, rfl⟩
          rw [hbot, Submodule.mem_bot] at this
          exact Subtype.ext this
        rw [Submodule.eq_bot_iff]
        intro v hv
        have : b.equivFun.symm v ∈ U' := ⟨v, hv, rfl⟩
        rw [hU'_bot, Submodule.mem_bot] at this
        exact b.equivFun.symm.injective (by simpa using this)
      · right
        have hle_n : n ≤ Module.finrank ℂ U'' := Nat.find_min' hex
          ⟨U'', hU''_le.trans hUW, hbot, hU''_L, rfl⟩
        have hge_n : Module.finrank ℂ U'' ≤ n := by
          rw [show n = Module.finrank ℂ U from hUdim.symm]
          exact Submodule.finrank_mono hU''_le
        have hU''_eq : U'' = U := Submodule.eq_of_le_of_finrank_eq hU''_le (by omega)
        have hU'_top : U' = ⊤ := by
          rw [eq_top_iff]
          intro u _
          have hu : (u : K → ℂ) ∈ U'' := hU''_eq.symm ▸ u.2
          rcases hu with ⟨w, hw, hwu⟩
          have : w = u := Subtype.ext hwu
          subst this
          exact hw
        rw [eq_top_iff]
        intro v _
        have hv : b.equivFun.symm v ∈ U' := hU'_top.symm ▸ Submodule.mem_top
        rcases hv with ⟨w, hw, hvw⟩
        have : w = v := b.equivFun.symm.injective hvw
        subst this
        exact hw
    obtain ⟨μ, A, Bmat, hAB, hBA, hAB_inter⟩ := hR.2.2.2 (Fin n) ρ hρ_mat hρ_irred
    have hρ_conj : ∀ x : K, ρ x = A * R μ x * Bmat := by
      intro x
      calc ρ x = ρ x * (A * Bmat) := by rw [hAB, Matrix.mul_one]
        _ = (ρ x * A) * Bmat := (Matrix.mul_assoc _ _ _).symm
        _ = (A * R μ x) * Bmat := by rw [hAB_inter x (Set.mem_univ _)]
    let a₀ : Fin n := ⟨0, hn_pos⟩
    let u : K → ℂ := (b a₀ : K → ℂ)
    have hu_Wperp : u ∈ Wperp := hUW (b a₀).2
    have hu_eq : ∀ g : K, u g = ∑ c : Fin n, ρ g⁻¹ c a₀ * (b c : K → ℂ) 1 := by
      intro g
      have h1 : u g = (L g⁻¹ u) 1 := by simp [u, L]
      have h2 : L_U g⁻¹ (b a₀) = ∑ c : Fin n, ρ g⁻¹ c a₀ • b c := by
        have := Matrix.toLin_self b b (ρ g⁻¹) a₀
        rwa [Matrix.toLin_toMatrix] at this
      rw [h1]
      have h3 : L g⁻¹ u = (L_U g⁻¹ (b a₀) : K → ℂ) := rfl
      rw [h3, h2]
      simp [Finset.sum_apply]
    have : Nonempty (B μ) := (hR.2.1 μ).1
    have hd_pos : (0 : ℝ) < Fintype.card (B μ) := Nat.cast_pos.mpr Fintype.card_pos
    have hK_pos : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
    have hsqrt_ne : (Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (div_pos hd_pos hK_pos)))
    let coeff : B μ → B μ → ℂ := fun i j =>
      (∑ c : Fin n, A c i * Bmat j a₀ * (b c : K → ℂ) 1) *
        (Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ)⁻¹
    have hu_in_W_eq : u = ∑ i : B μ, ∑ j : B μ, coeff i j • φ ⟨μ, j, i⟩ := by
      ext g
      rw [hu_eq g]
      simp only [hρ_conj g⁻¹, isUnitaryRep_inv_eq_conjTranspose (hR.1 μ) g, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, φ,
        fourierMatrix, Matrix.of_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
      have hswap :
          ∑ c : Fin n, (∑ j : B μ, (∑ i : B μ, A c i * star (R μ g j i)) * Bmat j a₀) *
            (b c : K → ℂ) 1 =
          ∑ i : B μ, ∑ j : B μ, (∑ c : Fin n, A c i * Bmat j a₀ * (b c : K → ℂ) 1) *
            star (R μ g j i) := by
        simp_rw [Finset.sum_mul]
        calc ∑ c : Fin n, ∑ j : B μ, ∑ i : B μ,
              A c i * star (R μ g j i) * Bmat j a₀ * (b c : K → ℂ) 1
            = ∑ j : B μ, ∑ c : Fin n, ∑ i : B μ,
              A c i * star (R μ g j i) * Bmat j a₀ * (b c : K → ℂ) 1 := Finset.sum_comm
          _ = ∑ j : B μ, ∑ i : B μ, ∑ c : Fin n,
              A c i * star (R μ g j i) * Bmat j a₀ * (b c : K → ℂ) 1 := by
                refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
          _ = ∑ i : B μ, ∑ j : B μ, ∑ c : Fin n,
              A c i * Bmat j a₀ * (b c : K → ℂ) 1 * star (R μ g j i) := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ =>
                  Finset.sum_congr rfl fun j _ =>
                    Finset.sum_congr rfl fun c _ => by ring
      simp only [Complex.star_def] at hswap
      rw [hswap]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [coeff]
      rw [mul_assoc, inv_mul_cancel_left₀ hsqrt_ne]
    have hu_W : u ∈ W := by
      rw [hu_in_W_eq]
      exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    have hu0 : u = 0 := hip_self_zero u (hu_Wperp u hu_W)
    have hb0 : b a₀ = 0 := Subtype.ext hu0
    exact b.ne_zero a₀ hb0
  have hproj : ∀ u : K → ℂ, u = ∑ a, (ip (φ a) u) • φ a := by
    intro u
    let w := ∑ a, (ip (φ a) u) • φ a
    have hw : w ∈ W := Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    have hdiff : u - w ∈ Wperp := by
      intro v hv
      refine Submodule.span_induction (p := fun v _ => ip v (u - w) = 0) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨b, rfl⟩
        have h1 : ip (φ b) (u - w) = ip (φ b) u - ip (φ b) w := by
          simp [ip, mul_sub, Finset.sum_sub_distrib]
        have h2 : ip (φ b) w = ip (φ b) u := by
          have hw_eval : ∀ g : K, w g = ∑ a, ip (φ a) u * φ a g := fun g => by
            simp only [w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          change (∑ g : K, star (φ b g) * w g) = ip (φ b) u
          simp_rw [hw_eval, Finset.mul_sum]
          rw [Finset.sum_comm]
          have h3 : ∀ a, ∑ g : K, star (φ b g) * (ip (φ a) u * φ a g) =
              ip (φ a) u * ip (φ b) (φ a) := fun a => by
            simp only [ip, Finset.mul_sum]
            refine Finset.sum_congr rfl fun g _ => by ring
          simp_rw [h3, hip_φ]
          rw [Finset.sum_eq_single b]
          · simp
          · intro a _ ha; simp [ha.symm]
          · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
        rw [h1, h2, sub_self]
      · simp [ip]
      · intro v₁ v₂ _ _ h₁ h₂
        have : ip (v₁ + v₂) (u - w) = ip v₁ (u - w) + ip v₂ (u - w) := by
          simp [ip, add_mul, Finset.sum_add_distrib]
        rw [this, h₁, h₂, add_zero]
      · intro c v _ hv
        have : ip (c • v) (u - w) = star c * ip v (u - w) := by
          simp only [ip, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring
        rw [this, hv, mul_zero]
    rw [hWperp_bot] at hdiff
    exact sub_eq_zero.mp hdiff
  ext g g'
  let δ : K → ℂ := fun x => if x = g' then 1 else 0
  have hsing := congr_fun (hproj δ) g
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have hip_sing : ∀ a, ip (φ a) δ = fourierMatrix R a g' := by
    intro a
    simp only [ip, φ, δ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      star_star]
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hip_sing] at hsing
  have hsing_g : δ g = if g = g' then 1 else 0 := rfl
  rw [hsing_g] at hsing
  convert hsing.symm using 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [φ, mul_comm]

private def identEquiv {ΛH ΛG : Type} (BH : ΛH → Type) (Nminus : ΛG → Finset ΛH) :
    (Σ μ : ΛG, AdBas BH Nminus μ × AdBas BH Nminus μ) ≃ RHSOut BH Nminus where
  toFun := ident BH Nminus
  invFun x := ⟨x.2.1.1.1, x.2.1.2, ⟨⟨x.1, x.2.1.1.2⟩, x.2.2⟩⟩
  left_inv o := by
    rcases o with ⟨μ, Q, ⟨⟨l, hl⟩, R⟩⟩
    rfl
  right_inv x := by
    rcases x with ⟨l, ⟨⟨μ, hl⟩, Q⟩, R⟩
    rfl

private theorem enc_mul_conjTranspose {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G)) :
    Enc H T * (Enc H T)ᴴ = 1 := by
  let e : T × H ≃ G := Equiv.ofBijective _ hT
  ext th₁ th₂
  simp only [Matrix.mul_apply, Enc, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  rw [Fintype.sum_equiv e.symm _ (fun th =>
    (if e th = (th₁.1 : G) * (th₁.2 : G) then (1 : ℂ) else 0) *
      star (if e th = (th₂.1 : G) * (th₂.2 : G) then (1 : ℂ) else 0)) (fun g => by simp [e])]
  have h1 : ∀ th, (if e th = (th₁.1 : G) * (th₁.2 : G) then (1 : ℂ) else 0) =
      if th = th₁ then 1 else 0 := fun th => by
    have : e th = (th₁.1 : G) * (th₁.2 : G) ↔ th = th₁ := by
      simpa [e] using e.injective.eq_iff
    simp [this]
  have h2 : ∀ th, (if e th = (th₂.1 : G) * (th₂.2 : G) then (1 : ℂ) else 0) =
      if th = th₂ then 1 else 0 := fun th => by
    have : e th = (th₂.1 : G) * (th₂.2 : G) ↔ th = th₂ := by
      simpa [e] using e.injective.eq_iff
    simp [this]
  simp_rw [h1, h2]
  simp [eq_comm]

private theorem enc_conjTranspose_mul {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G)) :
    (Enc H T)ᴴ * Enc H T = 1 := by
  let e : T × H ≃ G := Equiv.ofBijective _ hT
  ext g₁ g₂
  simp only [Matrix.mul_apply, Enc, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have h1 : ∀ th : T × H, (if g₁ = (th.1 : G) * (th.2 : G) then (1 : ℂ) else 0) =
      if th = e.symm g₁ then 1 else 0 := fun th => by
    have : g₁ = e th ↔ th = e.symm g₁ := by
      rw [eq_comm, ← e.eq_symm_apply, eq_comm]
    simpa [e] using if_congr this rfl rfl
  have h2 : ∀ th : T × H, (if g₂ = (th.1 : G) * (th.2 : G) then (1 : ℂ) else 0) =
      if th = e.symm g₂ then 1 else 0 := fun th => by
    have : g₂ = e th ↔ th = e.symm g₂ := by
      rw [eq_comm, ← e.eq_symm_apply, eq_comm]
    simpa [e] using if_congr this rfl rfl
  simp_rw [h1, h2]
  simp [e.symm.injective.eq_iff, eq_comm]

private theorem fourier_factorization {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (hRG : ∀ μ, IsMatRep (RG μ)) (hAd : IsSubgroupAdapted H BH Nminus RH RG) :
    fourierMatrix RG =
      ((UIndTensorI T BH Nminus RG * Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH)) *
        Enc H T).submatrix (ident BH Nminus) id := by
  let e : T × H ≃ G := Equiv.ofBijective _ hT
  have hcard : Fintype.card G = Fintype.card T * Fintype.card H := by
    rw [← Fintype.card_prod, Fintype.card_congr e]
  ext ⟨μ, Q, ⟨⟨l, hl⟩, R⟩⟩ g
  let p := e.symm g
  let t := p.1
  let h := p.2
  have hth_eq : g = (t : G) * (h : G) := (e.apply_symm_apply g).symm
  simp only [fourierMatrix, Matrix.of_apply, Matrix.submatrix_apply, id_eq, Matrix.mul_apply,
    Enc]
  have henc : ∀ th : T × H, (if g = (th.1 : G) * (th.2 : G) then (1 : ℂ) else 0) =
      if th = (t, h) then 1 else 0 := by
    intro th
    have : g = (th.1 : G) * (th.2 : G) ↔ th = (t, h) := by
      rw [hth_eq]
      exact ⟨fun heq => e.injective heq.symm, fun heq => by cases heq; rfl⟩
    exact if_congr this rfl rfl
  simp only [henc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [UIndTensorI, Matrix.of_apply, ident, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, UIndLam]
  have hsplit :
      ∑ inp : T × Σ l' : ΛH, BH l' × BH l',
        (if e_l : inp.2.1 = l then
          ((Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
            ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
            RG μ (inp.1 : G) Q ⟨⟨l, hl⟩, cast (congrArg BH e_l) inp.2.2.1⟩) *
            (if cast (congrArg BH e_l) inp.2.2.2 = R then 1 else 0)
        else 0) *
        ((if inp.1 = t then (1 : ℂ) else 0) *
          ((Real.sqrt ((Fintype.card (BH inp.2.1) : ℝ) / (Fintype.card H : ℝ)) : ℂ) *
            RH inp.2.1 h inp.2.2.1 inp.2.2.2)) =
      ∑ P : BH l,
        ((Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
          ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
          RG μ (t : G) Q ⟨⟨l, hl⟩, P⟩) *
          ((Real.sqrt ((Fintype.card (BH l) : ℝ) / (Fintype.card H : ℝ)) : ℂ) * RH l h P R) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single t]
    · rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single l]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [Finset.sum_eq_single R]
        · simp
        · intro R' _ hR'
          simp [hR']
        · intro hR'; exact False.elim (hR' (Finset.mem_univ _))
      · intro l' _ hl'
        simp [hl']
      · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
    · intro t' _ ht'
      simp [ht']
    · intro ht'; exact False.elim (ht' (Finset.mem_univ _))
  rw [hsplit]
  have hsqrt :
      (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
        ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
      (Real.sqrt ((Fintype.card (BH l) : ℝ) / (Fintype.card H : ℝ)) : ℂ) =
      (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) / (Fintype.card G : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    congr 2
    rw [hcard]
    push_cast
    have hd_ne : (Fintype.card (BH l) : ℝ) ≠ 0 := by
      have : Nonempty (BH l) := ⟨R⟩
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  have had_sum :
      ∑ P : BH l, RG μ (t : G) Q ⟨⟨l, hl⟩, P⟩ * RH l h P R =
        ∑ P' : AdBas BH Nminus μ, RG μ (t : G) Q P' * RG μ (h : G) P' ⟨⟨l, hl⟩, R⟩ := by
    symm
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single ⟨l, hl⟩]
    · refine Finset.sum_congr rfl fun P _ => ?_
      have := hAd μ h ⟨⟨l, hl⟩, P⟩ ⟨⟨l, hl⟩, R⟩
      rw [dif_pos rfl, cast_eq] at this
      rw [this]
    · intro l' _ hl'
      refine Finset.sum_eq_zero fun P' _ => ?_
      have := hAd μ h ⟨l', P'⟩ ⟨⟨l, hl⟩, R⟩
      simp only [dif_neg hl'] at this
      rw [this, mul_zero]
    · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
  calc (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) / (Fintype.card G : ℝ)) : ℂ) *
        RG μ g Q ⟨⟨l, hl⟩, R⟩
      = (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) / (Fintype.card G : ℝ)) : ℂ) *
          (∑ P' : AdBas BH Nminus μ, RG μ (t : G) Q P' * RG μ (h : G) P' ⟨⟨l, hl⟩, R⟩) := by
          rw [hth_eq, (hRG μ).2 (t : G) (h : G), Matrix.mul_apply]
    _ = (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) / (Fintype.card G : ℝ)) : ℂ) *
          ∑ P : BH l, RG μ (t : G) Q ⟨⟨l, hl⟩, P⟩ * RH l h P R := by rw [had_sum]
    _ = ∑ P : BH l,
          ((Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
            ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
            RG μ (t : G) Q ⟨⟨l, hl⟩, P⟩) *
            ((Real.sqrt ((Fintype.card (BH l) : ℝ) / (Fintype.card H : ℝ)) : ℂ) * RH l h P R) := by
          rw [← hsqrt, Finset.mul_sum]
          refine Finset.sum_congr rfl fun P _ => by ring

private theorem kronecker_conjTranspose {l m n p : Type}
    (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
    (Matrix.kronecker A B)ᴴ = Matrix.kronecker Aᴴ Bᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.conjTranspose_apply]

private theorem kronecker_mul {l m n p r s : Type} [Fintype m] [Fintype r]
    (A : Matrix l m ℂ) (B : Matrix p r ℂ) (C : Matrix m n ℂ) (D : Matrix r s ℂ) :
    Matrix.kronecker A B * Matrix.kronecker C D = Matrix.kronecker (A * C) (B * D) :=
  (Matrix.mul_kronecker_mul A C B D).symm

private theorem uindTensorI_unitary {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG) :
    (UIndTensorI T BH Nminus RG)ᴴ * UIndTensorI T BH Nminus RG = 1 ∧
      UIndTensorI T BH Nminus RG * (UIndTensorI T BH Nminus RG)ᴴ = 1 := by
  let eId := identEquiv BH Nminus
  let FG' : Matrix (RHSOut BH Nminus) G ℂ := (fourierMatrix RG).submatrix eId.symm id
  have hFG'_mul : FG' * FG'ᴴ = 1 := by
    have hFG := fourierMatrix_mul_conjTranspose hRG
    ext r₁ r₂
    simp only [FG', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.one_apply]
    have hentry :
        ∑ g : G, fourierMatrix RG (eId.symm r₁) g * star (fourierMatrix RG (eId.symm r₂) g) =
          (fourierMatrix RG * (fourierMatrix RG)ᴴ) (eId.symm r₁) (eId.symm r₂) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hentry, hFG, Matrix.one_apply]
    simp only [eId.symm.injective.eq_iff]
  have hFG'_unit : FG'ᴴ * FG' = 1 := by
    have hFG := fourierMatrix_conjTranspose_mul hRG
    ext g₁ g₂
    simp only [FG', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq]
    rw [Fintype.sum_equiv eId.symm _ (fun r => star (fourierMatrix RG r g₁) * fourierMatrix RG r g₂)
      fun _ => rfl]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congr_fun (congr_fun hFG g₁) g₂
  let K := Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH)
  have hK_mul : K * Kᴴ = 1 := by
    dsimp only [K]
    rw [kronecker_conjTranspose, Matrix.conjTranspose_one, kronecker_mul,
      Matrix.mul_one, fourierMatrix_mul_conjTranspose hRH]
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [Matrix.one_apply, h1, h2]
  have hK_mul' : Kᴴ * K = 1 := by
    dsimp only [K]
    rw [kronecker_conjTranspose, Matrix.conjTranspose_one, kronecker_mul,
      Matrix.mul_one, fourierMatrix_conjTranspose_mul hRH]
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [Matrix.one_apply, h1, h2]
  let M := K * Enc H T
  have hM_mul : M * Mᴴ = 1 := by
    calc M * Mᴴ = K * (Enc H T * (Enc H T)ᴴ) * Kᴴ := by
          simp [M, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = K * Kᴴ := by rw [enc_mul_conjTranspose H T hT, Matrix.mul_one]
      _ = 1 := hK_mul
  have hM_mul' : Mᴴ * M = 1 := by
    calc Mᴴ * M = (Enc H T)ᴴ * (Kᴴ * K) * Enc H T := by
          simp [M, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Enc H T)ᴴ * Enc H T := by rw [hK_mul', Matrix.mul_one]
      _ = 1 := enc_conjTranspose_mul H T hT
  have hfact := fourier_factorization H T hT BH Nminus RH RG (fun μ => (hRG.1 μ).1) hAd
  have hFG'_eq : FG' = UIndTensorI T BH Nminus RG * M := by
    ext r g
    dsimp only [FG', M, K]
    have hid : ident BH Nminus (eId.symm r) = r := eId.apply_symm_apply r
    rw [Matrix.submatrix_apply, id_eq, hfact, Matrix.submatrix_apply, id_eq,
      hid, Matrix.mul_assoc]
  have hU_eq : UIndTensorI T BH Nminus RG = FG' * Mᴴ := by
    calc UIndTensorI T BH Nminus RG
        = UIndTensorI T BH Nminus RG * (M * Mᴴ) := by rw [hM_mul, Matrix.mul_one]
      _ = (UIndTensorI T BH Nminus RG * M) * Mᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = FG' * Mᴴ := by rw [← hFG'_eq]
  have hU_ct : (UIndTensorI T BH Nminus RG)ᴴ = M * FG'ᴴ := by
    rw [hU_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  constructor
  · calc (UIndTensorI T BH Nminus RG)ᴴ * UIndTensorI T BH Nminus RG
        = (M * FG'ᴴ) * (FG' * Mᴴ) := by rw [hU_ct, hU_eq]
      _ = M * (FG'ᴴ * FG') * Mᴴ := by simp only [Matrix.mul_assoc]
      _ = M * Mᴴ := by rw [hFG'_unit, Matrix.mul_one]
      _ = 1 := hM_mul
  · calc UIndTensorI T BH Nminus RG * (UIndTensorI T BH Nminus RG)ᴴ
        = (FG' * Mᴴ) * (M * FG'ᴴ) := by rw [hU_ct, hU_eq]
      _ = FG' * (Mᴴ * M) * FG'ᴴ := by simp only [Matrix.mul_assoc]
      _ = FG' * FG'ᴴ := by rw [hM_mul', Matrix.mul_one]
      _ = 1 := hFG'_mul

private theorem uindLam_unitary {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG) (l : ΛH) :
    (UIndLam T BH Nminus RG l)ᴴ * UIndLam T BH Nminus RG l = 1 ∧
      UIndLam T BH Nminus RG l * (UIndLam T BH Nminus RG l)ᴴ = 1 := by
  have : Nonempty (BH l) := (hRH.2.1 l).1
  obtain ⟨R₀⟩ := ‹Nonempty (BH l)›
  have hU := uindTensorI_unitary H T hT BH Nminus RH hRH RG hRG hAd
  constructor
  · ext ⟨t₁, P₁⟩ ⟨t₂, P₂⟩
    have hentry := congr_fun (congr_fun hU.1 (t₁, ⟨l, P₁, R₀⟩)) (t₂, ⟨l, P₂, R₀⟩)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry ⊢
    have hred :
        ∑ out : RHSOut BH Nminus,
          star (UIndTensorI T BH Nminus RG out (t₁, ⟨l, P₁, R₀⟩)) *
            UIndTensorI T BH Nminus RG out (t₂, ⟨l, P₂, R₀⟩) =
        ∑ M : Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1,
          star (UIndLam T BH Nminus RG l M (t₁, P₁)) *
            UIndLam T BH Nminus RG l M (t₂, P₂) := by
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single l]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [Finset.sum_eq_single R₀]
        · simp [UIndTensorI]
        · intro R' _ hR'
          simp [UIndTensorI, hR'.symm]
        · intro hR'; exact False.elim (hR' (Finset.mem_univ _))
      · intro l' _ hl'
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [UIndTensorI, Ne.symm hl']
      · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
    rw [← hred, hentry]
    have heq : (t₁, (⟨l, (P₁, R₀)⟩ : Σ l : ΛH, BH l × BH l)) =
        (t₂, ⟨l, (P₂, R₀)⟩) ↔ (t₁, P₁) = (t₂, P₂) := by
      simp
    simp [heq]
  · ext M₁ M₂
    have hentry := congr_fun (congr_fun hU.2 ⟨l, M₁, R₀⟩) ⟨l, M₂, R₀⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry ⊢
    have hred :
        ∑ inp : T × Σ l' : ΛH, BH l' × BH l',
          UIndTensorI T BH Nminus RG ⟨l, M₁, R₀⟩ inp *
            star (UIndTensorI T BH Nminus RG ⟨l, M₂, R₀⟩ inp) =
        ∑ tP : T × BH l,
          UIndLam T BH Nminus RG l M₁ tP *
            star (UIndLam T BH Nminus RG l M₂ tP) := by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fintype.sum_sigma, Finset.sum_eq_single l]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [Finset.sum_eq_single R₀]
        · simp [UIndTensorI]
        · intro R' _ hR'
          simp [UIndTensorI, hR']
        · intro hR'; exact False.elim (hR' (Finset.mem_univ _))
      · intro l' _ hl'
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [UIndTensorI, hl']
      · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
    rw [← hred, hentry]
    have heq : (⟨l, (M₁, R₀)⟩ : RHSOut BH Nminus) = ⟨l, (M₂, R₀)⟩ ↔ M₁ = M₂ := by
      simp
    simp [heq]

/-! ### Part 2: Relabelling an irrep system, and Mackey transversal lemmas -/

private theorem repEquiv_symm {K ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : K → Matrix ι₁ ι₁ ℂ} {R₂ : K → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) : RepEquiv R₂ R₁ := by
  obtain ⟨A, B, hAB, hBA, hinter⟩ := h
  refine ⟨B, A, hBA, hAB, fun g _ => ?_⟩
  calc B * R₂ g = B * R₂ g * (A * B) := by rw [hAB, Matrix.mul_one]
    _ = B * (R₂ g * A) * B := by simp only [Matrix.mul_assoc]
    _ = B * (A * R₁ g) * B := by rw [(hinter g (Set.mem_univ _)).symm]
    _ = R₁ g * B := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]

private theorem repEquiv_trans {K ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
    {R₁ : K → Matrix ι₁ ι₁ ℂ} {R₂ : K → Matrix ι₂ ι₂ ℂ} {R₃ : K → Matrix ι₃ ι₃ ℂ}
    (h₁₂ : RepEquiv R₁ R₂) (h₂₃ : RepEquiv R₂ R₃) : RepEquiv R₁ R₃ := by
  obtain ⟨A₁, B₁, hAB₁, hBA₁, hint₁⟩ := h₁₂
  obtain ⟨A₂, B₂, hAB₂, hBA₂, hint₂⟩ := h₂₃
  refine ⟨A₂ * A₁, B₁ * B₂, ?_, ?_, fun g _ => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₁, hAB₁, Matrix.one_mul, hAB₂]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc B₂, hBA₂, Matrix.one_mul, hBA₁]
  · rw [Matrix.mul_assoc, hint₁ g (Set.mem_univ _), ← Matrix.mul_assoc,
      hint₂ g (Set.mem_univ _), Matrix.mul_assoc]

private theorem isIrrepSystem_relabel {K Λ : Type} [Monoid K]
    {B B' : Λ → Type} [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
    [∀ l, Fintype (B' l)] [∀ l, DecidableEq (B' l)]
    {R : ∀ l, K → Matrix (B l) (B l) ℂ} (hR : IsIrrepSystem R)
    (e : ∀ l, B l ≃ B' l) :
    IsIrrepSystem (fun l k => (R l k).submatrix (e l).symm (e l).symm) := by
  let R' : ∀ l, K → Matrix (B' l) (B' l) ℂ :=
    fun l k => (R l k).submatrix (e l).symm (e l).symm
  have hsub_one : ∀ l, (1 : Matrix (B l) (B l) ℂ).submatrix (e l).symm (e l).symm = 1 := by
    intro l; ext x y; simp [Matrix.one_apply, (e l).symm.injective.eq_iff]
  have hsub_mul : ∀ l (A C : Matrix (B l) (B l) ℂ),
      (A * C).submatrix (e l).symm (e l).symm =
        A.submatrix (e l).symm (e l).symm * C.submatrix (e l).symm (e l).symm := by
    intro l A C; ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    exact (Fintype.sum_equiv (e l).symm _ _ fun _ => rfl).symm
  have hunit : ∀ l, IsUnitaryRep (R' l) := by
    intro l
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show R' l 1 = 1
      dsimp [R']
      rw [(hR.1 l).1.1, hsub_one]
    · intro g h
      show R' l (g * h) = R' l g * R' l h
      dsimp [R']
      rw [(hR.1 l).1.2, hsub_mul]
    · intro k
      rw [Matrix.mem_unitaryGroup_iff]
      have hu := isUnitaryRep_mul_conjTranspose (hR.1 l) k
      have hct : star (R' l k) = ((R l k)ᴴ).submatrix (e l).symm (e l).symm := by
        ext x y; rfl
      rw [hct, ← hsub_mul, hu, hsub_one]
  have hirred : ∀ l, IsIrreducibleRep (R' l) := by
    intro l
    refine ⟨(hR.2.1 l).1.map (e l), fun W hW => ?_⟩
    let Φ : (B' l → ℂ) ≃ₗ[ℂ] (B l → ℂ) :=
      { toFun := fun v i => v (e l i)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun u j => u ((e l).symm j)
        left_inv := fun v => by ext j; simp
        right_inv := fun u => by ext i; simp }
    have hmulVec : ∀ k v, (R' l k).mulVec v = Φ.symm ((R l k).mulVec (Φ v)) := by
      intro k v; ext j
      simp only [R', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Φ, LinearEquiv.coe_symm_mk]
      exact Fintype.sum_equiv (e l).symm _ _ fun i => by simp
    have hW' : IsInvariantSubspace (R l) (W.map Φ.toLinearMap) := by
      intro k u hu
      rcases hu with ⟨v, hv, rfl⟩
      refine ⟨(R' l k).mulVec v, hW k v hv, ?_⟩
      rw [hmulVec]
      exact Φ.apply_symm_apply _
    rcases (hR.2.1 l).2 _ hW' with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have : Φ v ∈ W.map Φ.toLinearMap := ⟨v, hv, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      exact Φ.injective (by simpa using this)
    · right
      rw [eq_top_iff]
      intro v _
      have : Φ v ∈ W.map Φ.toLinearMap := htop.symm ▸ Submodule.mem_top
      rcases this with ⟨w, hw, hweq⟩
      have : w = v := Φ.injective hweq
      subst this
      exact hw
  have hequiv_self : ∀ l, RepEquiv (R' l) (R l) := by
    intro l
    let A : Matrix (B l) (B' l) ℂ := Matrix.of fun i j => if e l i = j then 1 else 0
    let Bmat : Matrix (B' l) (B l) ℂ := Matrix.of fun j i => if e l i = j then 1 else 0
    refine ⟨A, Bmat, ?_, ?_, fun k _ => ?_⟩
    · ext i i'
      simp only [A, Bmat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
      rw [Finset.sum_eq_single (e l i)]
      · simp [eq_comm]
      · intro j _ hj; simp [hj.symm]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    · ext j j'
      simp only [A, Bmat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
      rw [Finset.sum_eq_single ((e l).symm j)]
      · simp [(e l).apply_symm_apply j]
      · intro i _ hi
        have : e l i ≠ j := fun he => hi (by rw [← he, (e l).symm_apply_apply])
        simp [this]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    · ext i j'
      simp only [A, R', Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply]
      rw [Finset.sum_eq_single (e l i)]
      · simp only [if_true, one_mul]
        rw [Finset.sum_eq_single ((e l).symm j')]
        · simp
        · intro i' _ hi'
          have : e l i' ≠ j' := fun he => hi' (by rw [← he, (e l).symm_apply_apply])
          simp [this]
        · intro h; exact False.elim (h (Finset.mem_univ _))
      · intro j _ hj; simp [hj.symm]
      · intro h; exact False.elim (h (Finset.mem_univ _))
  refine ⟨hunit, hirred, ?_, ?_⟩
  · intro l l' hne hrep
    exact hR.2.2.1 l l' hne
      (repEquiv_trans (repEquiv_symm (hequiv_self l)) (repEquiv_trans hrep (hequiv_self l')))
  · intro ι _ _ ρ hρmat hρirr
    obtain ⟨l, hl⟩ := hR.2.2.2 ι ρ hρmat hρirr
    exact ⟨l, repEquiv_trans (hequiv_self l) hl⟩

private def mackeyMap {G : Type} [Group G] (H : Subgroup G) (Ω : Set G) (Tω : G → Set H) :
    (Σ ω : Ω, Tω ω.1) × H → G :=
  fun x => ((x.1.2 : H) : G) * (x.1.1 : G) * (x.2 : G)

private theorem mackeyMap_bijective {G : Type} [Group G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H)) :
    Function.Bijective (mackeyMap H Ω Tω) := by
  constructor
  · rintro ⟨⟨ω₁, a₁⟩, k₁⟩ ⟨⟨ω₂, a₂⟩, k₂⟩ heq
    dsimp [mackeyMap] at heq
    have hω_eq : ω₁ = ω₂ := by
      apply (hΩ (mackeyMap H Ω Tω ⟨⟨ω₁, a₁⟩, k₁⟩)).unique
      · exact ⟨a₁.1.1, a₁.1.2, k₁.1, k₁.2, rfl⟩
      · exact ⟨a₂.1.1, a₂.1.2, k₂.1, k₂.2, heq⟩
    subst hω_eq
    have hconj : ((a₂.1⁻¹ * a₁.1 : H) : G) = (ω₁ : G) * ((k₂ * k₁⁻¹ : H) : G) * (ω₁ : G)⁻¹ := by
      have h1 : (((a₁.1 : H) : G) * (ω₁ : G)) * (k₁ : G) =
          (((a₂.1 : H) : G) * (ω₁ : G)) * (k₂ : G) := heq
      calc ((a₂.1⁻¹ * a₁.1 : H) : G)
          = (a₂.1 : G)⁻¹ * ((a₁.1 : G) * (ω₁ : G) * (k₁ : G)) * (k₁ : G)⁻¹ * (ω₁ : G)⁻¹ := by
              simp [mul_assoc]
        _ = (a₂.1 : G)⁻¹ * ((a₂.1 : G) * (ω₁ : G) * (k₂ : G)) * (k₁ : G)⁻¹ * (ω₁ : G)⁻¹ := by
              rw [h1]
        _ = (ω₁ : G) * ((k₂ * k₁⁻¹ : H) : G) * (ω₁ : G)⁻¹ := by
              simp [mul_assoc]
    have hmem_inter : a₂.1⁻¹ * a₁.1 ∈ interSub H ω₁.1 := by
      change ((a₂.1⁻¹ * a₁.1 : H) : G) ∈ H.map (MulAut.conj ω₁.1).toMonoidHom
      rw [Subgroup.mem_map]
      refine ⟨(k₂ * k₁⁻¹ : H), (k₂ * k₁⁻¹).2, ?_⟩
      change (ω₁ : G) * ((k₂ * k₁⁻¹ : H) : G) * (ω₁ : G)⁻¹ = ((a₂.1⁻¹ * a₁.1 : H) : G)
      exact hconj.symm
    let z : interSub H ω₁.1 := ⟨a₂.1⁻¹ * a₁.1, hmem_inter⟩
    have ha_eq : (fun x : Tω ω₁.1 × interSub H ω₁.1 => (x.1 : H) * (x.2 : H)) ⟨a₁, 1⟩ =
        (fun x : Tω ω₁.1 × interSub H ω₁.1 => (x.1 : H) * (x.2 : H)) ⟨a₂, z⟩ := by
      ext1; simp [z]
    have hpair := (hTω ω₁.1 ω₁.2).1 ha_eq
    have ha : a₁ = a₂ := congrArg Prod.fst hpair
    have hz1 : (z : H) = 1 := congrArg (fun p => (p.2 : H)) hpair.symm
    have hk_eq : (ω₁ : G) * ((k₂ * k₁⁻¹ : H) : G) * (ω₁ : G)⁻¹ = 1 := by
      rw [← hconj, show ((a₂.1⁻¹ * a₁.1 : H) : G) = ((z : H) : G) from rfl, hz1]
      simp
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hk_eq
    have hk21 : (k₂ : G) * (k₁ : G)⁻¹ = 1 := by
      have hmul : (ω₁ : G)⁻¹ * ((ω₁ : G) * ((k₂ : G) * (k₁ : G)⁻¹) * (ω₁ : G)⁻¹) * (ω₁ : G) =
          (ω₁ : G)⁻¹ * 1 * (ω₁ : G) := by
        rw [hk_eq]
      simpa [mul_assoc] using hmul
    have hk : k₁ = k₂ := by
      ext1
      exact (mul_inv_eq_one.mp hk21).symm
    subst ha; subst hk; rfl
  · intro g
    obtain ⟨ω, h, hh, k, hk, hg⟩ := (hΩ g).exists
    obtain ⟨⟨a, z⟩, haz⟩ := (hTω ω.1 ω.2).2 ⟨h, hh⟩
    let z' : H := ⟨(ω : G)⁻¹ * ((z : H) : G) * (ω : G), interSub_conj_mem H ω.1 z⟩
    refine ⟨⟨⟨ω, a⟩, z' * ⟨k, hk⟩⟩, ?_⟩
    dsimp [mackeyMap]
    have hzw : ((z : H) : G) * (ω : G) = (ω : G) * (z' : G) := by
      simp [z', mul_assoc]
    have haz' : h = (a : G) * ((z : H) : G) := congrArg Subtype.val haz.symm
    calc ((a : H) : G) * (ω : G) * ((z' * ⟨k, hk⟩ : H) : G)
        = (a : G) * ((ω : G) * (z' : G)) * k := by simp [mul_assoc]
      _ = (a : G) * (((z : H) : G) * (ω : G)) * k := by rw [← hzw]
      _ = h * (ω : G) * k := by rw [← mul_assoc (a : G), ← haz']
      _ = g := hg.symm

private noncomputable def mackeyT_equiv {G : Type} [Group G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H)) :
    (Σ ω : Ω, Tω ω.1) ≃ mackeyT H Ω Tω :=
  Equiv.ofBijective
    (fun ⟨ω, a⟩ => ⟨((a : H) : G) * (ω : G), ⟨ω.1, ω.2, a.1, a.2, rfl⟩⟩)
    (by
      constructor
      · rintro ⟨ω₁, a₁⟩ ⟨ω₂, a₂⟩ heq
        have heqG : ((a₁ : H) : G) * (ω₁ : G) = ((a₂ : H) : G) * (ω₂ : G) :=
          congrArg Subtype.val heq
        have hmap : mackeyMap H Ω Tω (⟨ω₁, a₁⟩, 1) = mackeyMap H Ω Tω (⟨ω₂, a₂⟩, 1) := by
          simp [mackeyMap, heqG]
        exact congrArg Prod.fst ((mackeyMap_bijective H Ω hΩ Tω hTω).1 hmap)
      · rintro ⟨g, ω, hω, a, ha, rfl⟩
        exact ⟨⟨⟨ω, hω⟩, ⟨a, ha⟩⟩, rfl⟩)

private theorem mackeyT_isComplement {G : Type} [Group G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H)) :
    Subgroup.IsComplement (mackeyT H Ω Tω) (H : Set G) := by
  let e1 : (Σ ω : Ω, Tω ω.1) × H ≃ mackeyT H Ω Tω × (H : Set G) :=
    Equiv.prodCongr (mackeyT_equiv H Ω hΩ Tω hTω) (Equiv.refl H)
  have hcomp : (fun x : mackeyT H Ω Tω × (H : Set G) => (x.1 : G) * (x.2 : G)) ∘ e1 =
      mackeyMap H Ω Tω := by
    ext ⟨⟨ω, a⟩, k⟩
    rfl
  change Function.Bijective (fun x : mackeyT H Ω Tω × (H : Set G) => (x.1 : G) * (x.2 : G))
  rw [← Equiv.bijective_comp e1, hcomp]
  exact mackeyMap_bijective H Ω hΩ Tω hTω

private theorem card_complement_eq_index {G : Type} [Group G] [Fintype G]
    (K : Subgroup G) [Fintype K] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (K : Set G)) :
    Fintype.card T = K.index := by
  have h1 : Fintype.card T * Fintype.card K = Fintype.card G := by
    have hc := hT.card_mul_card
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hc
  have h2 : K.index * Fintype.card K = Fintype.card G := by
    have hi := K.index_mul_card
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hi
  have hK_pos : 0 < Fintype.card K := Fintype.card_pos
  exact Nat.mul_right_cancel hK_pos (h1.trans h2.symm)

/-! ### Part 3: Unitarity of `Nop l` -/

private theorem nop_apply_mackeyT {G : Type} [Group G] [Fintype G] {H : Subgroup G} {Ω : Set G}
    {hΩ : IsDoubleCosetTransversal H H Ω} {Tω : G → Set H}
    {hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H)}
    {ΛH : Type} [Fintype ΛH] {BH : ΛH → Type} [∀ l, Fintype (BH l)] [∀ l, DecidableEq (BH l)]
    {RH : ∀ l, H → Matrix (BH l) (BH l) ℂ}
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] {Bω : ∀ ω, Λω ω → Type}
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    {NmW : ∀ ω, ΛH → Finset (Λω ω)} {adapt : ∀ ω l, BH l ≃ AdBas (Bω ω) (NmW ω) l}
    {Ntw : ∀ ω, ΛH → Finset (Λω ω)} {Utw : ∀ ω l, Matrix (Σ κ : Ntw ω l, Bω ω κ.1) (BH l) ℂ}
    {l : ΛH} (o : NOut Ω BH NmW Ntw (Λω := Λω) l) (ω' : Ω) (a' : Tω ω'.1) (P : BH l) :
    Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l o
      (mackeyT_equiv H Ω hΩ Tω hTω ⟨ω', a'⟩, P) =
      if e : o.1 = ω' then
        ∑ Pt : Bω o.1.1 o.2.1.1,
          UIndLam (Tω o.1.1) (Bω o.1.1) (NmW o.1.1) (RHad H BH RH Bω NmW adapt o.1.1) o.2.1.1
              ⟨⟨o.2.2.1.1, o.2.2.1.2⟩, adapt o.1.1 o.2.2.1.1 o.2.2.2⟩
              (e ▸ a', Pt) *
            Utw o.1.1 l ⟨o.2.1, Pt⟩ P
      else 0 := by
  let eM := mackeyT_equiv H Ω hΩ Tω hTω
  simp only [Nop, Matrix.of_apply]
  by_cases he : o.1 = ω'
  · subst he
    have hex : ∃ a : Tω o.1.1, ((a : H) : G) * (o.1 : G) = (eM ⟨o.1, a'⟩ : G) :=
      ⟨a', rfl⟩
    rw [dif_pos hex, dif_pos rfl]
    have hch : Classical.choose hex = a' := by
      have hval : eM ⟨o.1, Classical.choose hex⟩ = eM ⟨o.1, a'⟩ := by
        ext1
        exact Classical.choose_spec hex
      exact eq_of_heq (Sigma.ext_iff.mp (eM.injective hval)).2
    rw [hch]
  · have hnex : ¬ ∃ a : Tω o.1.1, ((a : H) : G) * (o.1 : G) = (eM ⟨ω', a'⟩ : G) := by
      rintro ⟨a, ha⟩
      have hval : eM ⟨o.1, a⟩ = eM ⟨ω', a'⟩ := Subtype.ext ha
      exact he (congrArg Sigma.fst (eM.injective hval))
    rw [dif_neg hnex, dif_neg he]

private theorem nop_unitary {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH : Type} [Fintype ΛH] (BH : ΛH → Type) [∀ l, Fintype (BH l)] [∀ l, DecidableEq (BH l)]
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (NmW : ∀ ω, ΛH → Finset (Λω ω)) (adapt : ∀ ω l, BH l ≃ AdBas (Bω ω) (NmW ω) l)
    (hAdω : ∀ ω ∈ Ω, IsAdaptedToInter H BH RH Bω Rω NmW adapt ω)
    (Ntw : ∀ ω, ΛH → Finset (Λω ω)) (Utw : ∀ ω l, Matrix (Σ κ : Ntw ω l, Bω ω κ.1) (BH l) ℂ)
    (hUtw : ∀ ω ∈ Ω, ∀ l, IsUntwisting H BH RH Bω Rω Ntw Utw ω l) (l : ΛH) :
    Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l *
        (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ = 1 ∧
      (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ *
        Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l = 1 := by
  let eM := mackeyT_equiv H Ω hΩ Tω hTω
  have hRHad_sys : ∀ ω : Ω, IsIrrepSystem (RHad H BH RH Bω NmW adapt ω.1) := by
    intro ω
    exact isIrrepSystem_relabel hRH (adapt ω.1)
  have hUInd_unit : ∀ (ω : Ω) (κ : Λω ω.1),
      (UIndLam (Tω ω.1) (Bω ω.1) (NmW ω.1) (RHad H BH RH Bω NmW adapt ω.1) κ)ᴴ *
        UIndLam (Tω ω.1) (Bω ω.1) (NmW ω.1) (RHad H BH RH Bω NmW adapt ω.1) κ = 1 ∧
      UIndLam (Tω ω.1) (Bω ω.1) (NmW ω.1) (RHad H BH RH Bω NmW adapt ω.1) κ *
        (UIndLam (Tω ω.1) (Bω ω.1) (NmW ω.1) (RHad H BH RH Bω NmW adapt ω.1) κ)ᴴ = 1 := by
    intro ω κ
    convert uindLam_unitary (interSub H ω.1) (Tω ω.1) (hTω ω.1 ω.2) (Bω ω.1) (NmW ω.1)
      (Rω ω.1) (hRω ω.1 ω.2) (RHad H BH RH Bω NmW adapt ω.1) (hRHad_sys ω) (hAdω ω.1 ω.2) κ
  constructor
  · ext o₁ o₂
    rcases o₁ with ⟨ω₁, κ₁, lt₁, Q₁⟩
    rcases o₂ with ⟨ω₂, κ₂, lt₂, Q₂⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_equiv eM.symm _ (fun x => ∑ P : BH l,
      Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₁, κ₁, lt₁, Q₁⟩ (eM x, P) *
        star (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₂, κ₂, lt₂, Q₂⟩ (eM x, P)))
      (fun t => by simp [eM.apply_symm_apply])]
    rw [Fintype.sum_sigma]
    by_cases hω : ω₁ = ω₂
    · subst hω
      rw [Finset.sum_eq_single ω₁]
      · have hnop1 : ∀ (a : Tω ω₁.1) (P : BH l),
            Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₁, κ₁, lt₁, Q₁⟩ (eM ⟨ω₁, a⟩, P) =
              ∑ Pt₁ : Bω ω₁.1 κ₁.1,
                UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₁.1
                  ⟨⟨lt₁.1, lt₁.2⟩, adapt ω₁.1 lt₁.1 Q₁⟩ (a, Pt₁) *
                Utw ω₁.1 l ⟨κ₁, Pt₁⟩ P := by
          intro a P
          rw [nop_apply_mackeyT ⟨ω₁, κ₁, lt₁, Q₁⟩ ω₁ a P, dif_pos rfl]
        have hnop2 : ∀ (a : Tω ω₁.1) (P : BH l),
            Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₁, κ₂, lt₂, Q₂⟩ (eM ⟨ω₁, a⟩, P) =
              ∑ Pt₂ : Bω ω₁.1 κ₂.1,
                UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₂.1
                  ⟨⟨lt₂.1, lt₂.2⟩, adapt ω₁.1 lt₂.1 Q₂⟩ (a, Pt₂) *
                Utw ω₁.1 l ⟨κ₂, Pt₂⟩ P := by
          intro a P
          rw [nop_apply_mackeyT ⟨ω₁, κ₂, lt₂, Q₂⟩ ω₁ a P, dif_pos rfl]
        simp_rw [hnop1, hnop2]
        have hswap :
            ∑ a : Tω ω₁.1, ∑ P : BH l,
              (∑ Pt₁ : Bω ω₁.1 κ₁.1,
                UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₁.1
                  ⟨⟨lt₁.1, lt₁.2⟩, adapt ω₁.1 lt₁.1 Q₁⟩ (a, Pt₁) *
                Utw ω₁.1 l ⟨κ₁, Pt₁⟩ P) *
              star (∑ Pt₂ : Bω ω₁.1 κ₂.1,
                UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₂.1
                  ⟨⟨lt₂.1, lt₂.2⟩, adapt ω₁.1 lt₂.1 Q₂⟩ (a, Pt₂) *
                Utw ω₁.1 l ⟨κ₂, Pt₂⟩ P) =
            ∑ a : Tω ω₁.1, ∑ Pt₁ : Bω ω₁.1 κ₁.1, ∑ Pt₂ : Bω ω₁.1 κ₂.1,
              UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₁.1
                ⟨⟨lt₁.1, lt₁.2⟩, adapt ω₁.1 lt₁.1 Q₁⟩ (a, Pt₁) *
              star (UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₂.1
                ⟨⟨lt₂.1, lt₂.2⟩, adapt ω₁.1 lt₂.1 Q₂⟩ (a, Pt₂)) *
              (Utw ω₁.1 l * (Utw ω₁.1 l)ᴴ) ⟨κ₁, Pt₁⟩ ⟨κ₂, Pt₂⟩ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [Complex.star_def]
          simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun Pt₁ _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun Pt₂ _ => ?_
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.mul_sum]
          refine Finset.sum_congr rfl fun P _ => ?_
          ring
        rw [hswap, (hUtw ω₁.1 ω₁.2 l).1]
        by_cases hκ : κ₁ = κ₂
        · subst hκ
          have hcollapse :
              ∑ a : Tω ω₁.1, ∑ Pt₁ : Bω ω₁.1 κ₁.1, ∑ Pt₂ : Bω ω₁.1 κ₁.1,
                UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₁.1
                  ⟨⟨lt₁.1, lt₁.2⟩, adapt ω₁.1 lt₁.1 Q₁⟩ (a, Pt₁) *
                star (UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₁.1
                  ⟨⟨lt₂.1, lt₂.2⟩, adapt ω₁.1 lt₂.1 Q₂⟩ (a, Pt₂)) *
                (1 : Matrix (Σ κ : Ntw ω₁.1 l, Bω ω₁.1 κ.1) (Σ κ : Ntw ω₁.1 l, Bω ω₁.1 κ.1) ℂ)
                  ⟨κ₁, Pt₁⟩ ⟨κ₁, Pt₂⟩ =
              (UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₁.1 *
                (UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₁.1)ᴴ)
                  ⟨⟨lt₁.1, lt₁.2⟩, adapt ω₁.1 lt₁.1 Q₁⟩ ⟨⟨lt₂.1, lt₂.2⟩, adapt ω₁.1 lt₂.1 Q₂⟩ := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun a _ => ?_
            refine Finset.sum_congr rfl fun Pt₁ _ => ?_
            rw [Finset.sum_eq_single Pt₁]
            · simp [Matrix.conjTranspose_apply]
            · intro Pt₂ _ hPt
              have hne : (⟨κ₁, Pt₁⟩ : Σ κ : Ntw ω₁.1 l, Bω ω₁.1 κ.1) ≠ ⟨κ₁, Pt₂⟩ := by
                intro heq; exact hPt (eq_of_heq (Sigma.ext_iff.mp heq).2).symm
              simp [hne]
            · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
          rw [hcollapse, (hUInd_unit ω₁ κ₁.1).2, Matrix.one_apply]
          have hiff :
              (⟨⟨lt₁.1, lt₁.2⟩, adapt ω₁.1 lt₁.1 Q₁⟩ :
                  Σ lt : {lt : ΛH // κ₁.1 ∈ NmW ω₁.1 lt}, AdBas (Bω ω₁.1) (NmW ω₁.1) lt.1) =
                ⟨⟨lt₂.1, lt₂.2⟩, adapt ω₁.1 lt₂.1 Q₂⟩ ↔
              (⟨ω₁, κ₁, lt₁, Q₁⟩ : NOut Ω BH NmW Ntw (Λω := Λω) l) = ⟨ω₁, κ₁, lt₂, Q₂⟩ := by
            constructor
            · intro heq
              have hlt : lt₁ = lt₂ := by
                have := congrArg Sigma.fst heq
                exact Subtype.ext (congrArg Subtype.val this)
              rcases lt₁ with ⟨lt₁v, hlt1⟩
              rcases lt₂ with ⟨lt₂v, hlt2⟩
              have hltv : lt₁v = lt₂v := congrArg Subtype.val hlt
              subst hltv
              have hQeq : adapt ω₁.1 lt₁v Q₁ = adapt ω₁.1 lt₁v Q₂ :=
                eq_of_heq (Sigma.ext_iff.mp heq).2
              have hQ : Q₁ = Q₂ := (adapt ω₁.1 lt₁v).injective hQeq
              subst hQ; rfl
            · intro heq
              rcases lt₁ with ⟨lt₁v, hlt1⟩
              rcases lt₂ with ⟨lt₂v, hlt2⟩
              have hlt : lt₁v = lt₂v := congrArg (fun x => x.2.2.1.1) heq
              subst hlt
              have hQ : Q₁ = Q₂ := eq_of_heq (Sigma.ext_iff.mp (eq_of_heq
                (Sigma.ext_iff.mp (eq_of_heq (Sigma.ext_iff.mp heq).2)).2)).2
              subst hQ; rfl
          exact if_congr hiff rfl rfl
        · have hzero :
              ∑ a : Tω ω₁.1, ∑ Pt₁ : Bω ω₁.1 κ₁.1, ∑ Pt₂ : Bω ω₁.1 κ₂.1,
                UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₁.1
                  ⟨⟨lt₁.1, lt₁.2⟩, adapt ω₁.1 lt₁.1 Q₁⟩ (a, Pt₁) *
                star (UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ₂.1
                  ⟨⟨lt₂.1, lt₂.2⟩, adapt ω₁.1 lt₂.1 Q₂⟩ (a, Pt₂)) *
                (1 : Matrix (Σ κ : Ntw ω₁.1 l, Bω ω₁.1 κ.1) (Σ κ : Ntw ω₁.1 l, Bω ω₁.1 κ.1) ℂ)
                  ⟨κ₁, Pt₁⟩ ⟨κ₂, Pt₂⟩ = 0 := by
            refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun Pt₁ _ =>
              Finset.sum_eq_zero fun Pt₂ _ => ?_
            have hne : (⟨κ₁, Pt₁⟩ : Σ κ : Ntw ω₁.1 l, Bω ω₁.1 κ.1) ≠ ⟨κ₂, Pt₂⟩ := fun heq =>
              hκ (congrArg Sigma.fst heq)
            simp [hne]
          have hne_o : (⟨ω₁, κ₁, lt₁, Q₁⟩ : NOut Ω BH NmW Ntw (Λω := Λω) l) ≠
              ⟨ω₁, κ₂, lt₂, Q₂⟩ := fun heq =>
            hκ (congrArg Sigma.fst (eq_of_heq (Sigma.ext_iff.mp heq).2))
          rw [hzero, if_neg hne_o]
      · intro ω' _ hω'
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun P _ => ?_
        rw [nop_apply_mackeyT ⟨ω₁, κ₁, lt₁, Q₁⟩ ω' a P, dif_neg (Ne.symm hω'), zero_mul]
      · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
    · have hzero :
          ∑ ω' : Ω, ∑ x : Tω ω'.1, ∑ P : BH l,
            Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₁, κ₁, lt₁, Q₁⟩ (eM ⟨ω', x⟩, P) *
              star (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₂, κ₂, lt₂, Q₂⟩ (eM ⟨ω', x⟩, P)) =
            0 := by
        refine Finset.sum_eq_zero fun ω' _ => Finset.sum_eq_zero fun a _ =>
          Finset.sum_eq_zero fun P _ => ?_
        by_cases h1 : ω₁ = ω'
        · have h2 : ω₂ ≠ ω' := fun h => hω (h1.trans h.symm)
          rw [nop_apply_mackeyT ⟨ω₂, κ₂, lt₂, Q₂⟩ ω' a P, dif_neg h2, star_zero, mul_zero]
        · rw [nop_apply_mackeyT ⟨ω₁, κ₁, lt₁, Q₁⟩ ω' a P, dif_neg h1, zero_mul]
      have hne_o : (⟨ω₁, κ₁, lt₁, Q₁⟩ : NOut Ω BH NmW Ntw (Λω := Λω) l) ≠
          ⟨ω₂, κ₂, lt₂, Q₂⟩ := fun heq => hω (congrArg Sigma.fst heq)
      rw [hzero, if_neg hne_o]
  · ext ⟨t₁, P₁⟩ ⟨t₂, P₂⟩
    obtain ⟨⟨ω₁, a₁⟩, rfl⟩ := eM.surjective t₁
    obtain ⟨⟨ω₂, a₂⟩, rfl⟩ := eM.surjective t₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [Fintype.sum_sigma]
    by_cases hω : ω₁ = ω₂
    · subst hω
      rw [Finset.sum_eq_single ω₁]
      · rw [Fintype.sum_sigma]
        have hstep :
            ∀ κ : Ntw ω₁.1 l,
              ∑ x : (Σ lt : {lt : ΛH // κ.1 ∈ NmW ω₁.1 lt}, BH lt.1),
                star (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₁, κ, x⟩ (eM ⟨ω₁, a₁⟩, P₁)) *
                  Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₁, κ, x⟩ (eM ⟨ω₁, a₂⟩, P₂) =
              ∑ Pt : Bω ω₁.1 κ.1,
                star (Utw ω₁.1 l ⟨κ, Pt⟩ P₁) * Utw ω₁.1 l ⟨κ, Pt⟩ P₂ *
                  (if a₁ = a₂ then 1 else 0) := by
          intro κ
          have hnop1 : ∀ x : (Σ lt : {lt : ΛH // κ.1 ∈ NmW ω₁.1 lt}, BH lt.1),
              Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₁, κ, x⟩ (eM ⟨ω₁, a₁⟩, P₁) =
                ∑ Pt₁ : Bω ω₁.1 κ.1,
                  UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ.1
                    ⟨⟨x.1.1, x.1.2⟩, adapt ω₁.1 x.1.1 x.2⟩ (a₁, Pt₁) *
                  Utw ω₁.1 l ⟨κ, Pt₁⟩ P₁ := by
            intro x
            rw [nop_apply_mackeyT ⟨ω₁, κ, x⟩ ω₁ a₁ P₁, dif_pos rfl]
          have hnop2 : ∀ x : (Σ lt : {lt : ΛH // κ.1 ∈ NmW ω₁.1 lt}, BH lt.1),
              Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω₁, κ, x⟩ (eM ⟨ω₁, a₂⟩, P₂) =
                ∑ Pt₂ : Bω ω₁.1 κ.1,
                  UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ.1
                    ⟨⟨x.1.1, x.1.2⟩, adapt ω₁.1 x.1.1 x.2⟩ (a₂, Pt₂) *
                  Utw ω₁.1 l ⟨κ, Pt₂⟩ P₂ := by
            intro x
            rw [nop_apply_mackeyT ⟨ω₁, κ, x⟩ ω₁ a₂ P₂, dif_pos rfl]
          simp_rw [hnop1, hnop2]
          have hswap :
              ∑ x : (Σ lt : {lt : ΛH // κ.1 ∈ NmW ω₁.1 lt}, BH lt.1),
                star (∑ Pt₁ : Bω ω₁.1 κ.1,
                  UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ.1
                    ⟨⟨x.1.1, x.1.2⟩, adapt ω₁.1 x.1.1 x.2⟩ (a₁, Pt₁) *
                  Utw ω₁.1 l ⟨κ, Pt₁⟩ P₁) *
                (∑ Pt₂ : Bω ω₁.1 κ.1,
                  UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ.1
                    ⟨⟨x.1.1, x.1.2⟩, adapt ω₁.1 x.1.1 x.2⟩ (a₂, Pt₂) *
                  Utw ω₁.1 l ⟨κ, Pt₂⟩ P₂) =
              ∑ Pt₁ : Bω ω₁.1 κ.1, ∑ Pt₂ : Bω ω₁.1 κ.1,
                star (Utw ω₁.1 l ⟨κ, Pt₁⟩ P₁) * Utw ω₁.1 l ⟨κ, Pt₂⟩ P₂ *
                  ((UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ.1)ᴴ *
                    UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1) (RHad H BH RH Bω NmW adapt ω₁.1) κ.1)
                    (a₁, Pt₁) (a₂, Pt₂) := by
            simp only [Complex.star_def]
            simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun Pt₁ _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun Pt₂ _ => ?_
            let eAd : (Σ lt : {lt : ΛH // κ.1 ∈ NmW ω₁.1 lt}, BH lt.1) ≃
                (Σ lt : {lt : ΛH // κ.1 ∈ NmW ω₁.1 lt}, AdBas (Bω ω₁.1) (NmW ω₁.1) lt.1) :=
              Equiv.sigmaCongrRight (fun lt => adapt ω₁.1 lt.1)
            rw [Matrix.mul_apply, Fintype.sum_equiv eAd _ (fun y =>
              star (Utw ω₁.1 l ⟨κ, Pt₁⟩ P₁) * Utw ω₁.1 l ⟨κ, Pt₂⟩ P₂ *
                (star (UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1)
                  (RHad H BH RH Bω NmW adapt ω₁.1) κ.1 y (a₁, Pt₁)) *
                UIndLam (Tω ω₁.1) (Bω ω₁.1) (NmW ω₁.1)
                  (RHad H BH RH Bω NmW adapt ω₁.1) κ.1 y (a₂, Pt₂))) (fun x => by
              simp [eAd]; ring)]
            rw [← Finset.mul_sum]
            rfl
          rw [hswap, (hUInd_unit ω₁ κ.1).1]
          refine Finset.sum_congr rfl fun Pt₁ _ => ?_
          rw [Finset.sum_eq_single Pt₁]
          · simp [Matrix.one_apply, Prod.mk.injEq]
          · intro Pt₂ _ hPt
            have hne : (a₁, Pt₁) ≠ (a₂, Pt₂) := fun heq =>
              hPt (congrArg Prod.snd heq).symm
            simp [hne]
          · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
        simp_rw [hstep]
        by_cases ha : a₁ = a₂
        · subst ha
          simp only [if_true, mul_one]
          have hutw :
              ∑ κ : Ntw ω₁.1 l, ∑ Pt : Bω ω₁.1 κ.1,
                star (Utw ω₁.1 l ⟨κ, Pt⟩ P₁) * Utw ω₁.1 l ⟨κ, Pt⟩ P₂ =
              ((Utw ω₁.1 l)ᴴ * Utw ω₁.1 l) P₁ P₂ := by
            rw [Matrix.mul_apply, Fintype.sum_sigma]
            rfl
          rw [hutw, (hUtw ω₁.1 ω₁.2 l).2.1, Matrix.one_apply]
          simp [Prod.mk.injEq]
        · have hzero :
              ∑ κ : Ntw ω₁.1 l, ∑ Pt : Bω ω₁.1 κ.1,
                star (Utw ω₁.1 l ⟨κ, Pt⟩ P₁) * Utw ω₁.1 l ⟨κ, Pt⟩ P₂ *
                  (if a₁ = a₂ then (1 : ℂ) else 0) = 0 := by
            simp [ha]
          have hne_tp : (eM ⟨ω₁, a₁⟩, P₁) ≠ (eM ⟨ω₁, a₂⟩, P₂) := fun heq =>
            ha (eq_of_heq (Sigma.ext_iff.mp (eM.injective (congrArg Prod.fst heq))).2)
          rw [hzero, if_neg hne_tp]
      · intro ω _ hω'
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [nop_apply_mackeyT ⟨ω, x⟩ ω₁ a₁ P₁]
        dsimp only
        rw [dif_neg hω', star_zero, zero_mul]
      · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
    · have hzero :
          ∑ ω : Ω, ∑ x : (Σ κ : Ntw ω.1 l, Σ lt : {lt : ΛH // κ.1 ∈ NmW ω.1 lt}, BH lt.1),
            star (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω, x⟩ (eM ⟨ω₁, a₁⟩, P₁)) *
              Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l ⟨ω, x⟩ (eM ⟨ω₂, a₂⟩, P₂) = 0 := by
        refine Finset.sum_eq_zero fun ω _ => Finset.sum_eq_zero fun x _ => ?_
        by_cases h1 : ω = ω₁
        · have h2 : ω ≠ ω₂ := fun h => hω (h1.symm.trans h)
          rw [nop_apply_mackeyT ⟨ω, x⟩ ω₂ a₂ P₂]
          dsimp only
          rw [dif_neg h2, mul_zero]
        · rw [nop_apply_mackeyT ⟨ω, x⟩ ω₁ a₁ P₁]
          dsimp only
          rw [dif_neg h1, star_zero, zero_mul]
      have hne_tp : (eM ⟨ω₁, a₁⟩, P₁) ≠ (eM ⟨ω₂, a₂⟩, P₂) := fun heq =>
        hω (congrArg Sigma.fst (eM.injective (congrArg Prod.fst heq)))
      rw [hzero, if_neg hne_tp]

/-! ### Part 4: Computing `UIndLam * Nopᴴ = Aop` -/

private theorem twistRep_mul_conjTranspose_utw {G : Type} [Group G]
    (H : Subgroup G) (ω : G) {ΛH : Type} (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)]
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
    {Λω : G → Type} (Bω : ∀ ω, Λω ω → Type) [∀ ω κ, Fintype (Bω ω κ)]
    [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (Ntw : ∀ ω, ΛH → Finset (Λω ω)) (Utw : ∀ ω l, Matrix (Σ κ : Ntw ω l, Bω ω κ.1) (BH l) ℂ)
    (l : ΛH) (hUtw : IsUntwisting H BH RH Bω Rω Ntw Utw ω l)
    (h : interSub H ω) (P' : BH l) (κ : Ntw ω l) (Pt : Bω ω κ.1) :
    ∑ P : BH l, twistRep H ω (RH l) h P' P * conj (Utw ω l ⟨κ, Pt⟩ P) =
      ∑ Pt' : Bω ω κ.1, conj (Utw ω l ⟨κ, Pt'⟩ P') * Rω ω κ.1 h Pt' Pt := by
  have hmul : twistRep H ω (RH l) h * (Utw ω l)ᴴ =
      (Utw ω l)ᴴ * Matrix.of (fun (x y : Σ κ : Ntw ω l, Bω ω κ.1) =>
        if e : x.1 = y.1 then Rω ω y.1.1 h (cast (congrArg (fun κ => Bω ω κ.1) e) x.2) y.2
        else 0) := by
    calc twistRep H ω (RH l) h * (Utw ω l)ᴴ
        = ((Utw ω l)ᴴ * Utw ω l) * (twistRep H ω (RH l) h * (Utw ω l)ᴴ) := by
            rw [hUtw.2.1, Matrix.one_mul]
      _ = (Utw ω l)ᴴ * (Utw ω l * twistRep H ω (RH l) h * (Utw ω l)ᴴ) := by
            simp only [Matrix.mul_assoc]
      _ = (Utw ω l)ᴴ * Matrix.of _ := by congr 1; exact hUtw.2.2 h
  have hentry := congr_fun (congr_fun hmul P') ⟨κ, Pt⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def] at hentry
  rw [Fintype.sum_sigma, Finset.sum_eq_single κ] at hentry
  · convert hentry using 1
    refine Finset.sum_congr rfl fun Pt' _ => ?_
    simp
  · intro κ' _ hκ'
    refine Finset.sum_eq_zero fun Pt' _ => ?_
    simp [dif_neg hκ']
  · intro hmem; exact False.elim (hmem (Finset.mem_univ _))

private theorem sum_Tω_RH_mul_conj {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (Ω : Set G) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH : Type} [Fintype ΛH] (BH : ΛH → Type) [∀ l, Fintype (BH l)] [∀ l, DecidableEq (BH l)]
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (NmW : ∀ ω, ΛH → Finset (Λω ω)) (adapt : ∀ ω l, BH l ≃ AdBas (Bω ω) (NmW ω) l)
    (hAdω : ∀ ω ∈ Ω, IsAdaptedToInter H BH RH Bω Rω NmW adapt ω)
    (ω : Ω) (κ : Λω ω.1) (lt₁ lt₂ : ΛH) (h₁ : κ ∈ NmW ω.1 lt₁) (h₂ : κ ∈ NmW ω.1 lt₂)
    (Q₁ : BH lt₁) (Q₂ : BH lt₂) :
    ∑ a : Tω ω.1, ∑ Pt : Bω ω.1 κ,
      RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt⟩) *
        star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt⟩)) =
      if e : lt₁ = lt₂ then
        (if cast (congrArg BH e) Q₁ = Q₂ then
          (((Fintype.card (Tω ω.1) : ℂ) * (Fintype.card (Bω ω.1 κ) : ℂ)) /
            (Fintype.card (BH lt₁) : ℂ))
        else 0)
      else 0 := by
  have : Nonempty (Bω ω.1 κ) := ((hRω ω.1 ω.2).2.1 κ).1
  obtain ⟨Pt₀⟩ := ‹Nonempty (Bω ω.1 κ)›
  let eT : Tω ω.1 × interSub H ω.1 ≃ H := Equiv.ofBijective _ (hTω ω.1 ω.2)
  let S : ℂ := ∑ x : H,
    RH lt₁ x Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₀⟩) *
      star (RH lt₂ x Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₀⟩))
  have hS_split :
      S = ((Fintype.card (interSub H ω.1) : ℂ) / (Fintype.card (Bω ω.1 κ) : ℂ)) *
        ∑ a : Tω ω.1, ∑ Pt : Bω ω.1 κ,
          RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt⟩) *
            star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt⟩)) := by
    have h1 : ∀ (lt : ΛH) (h_lt : κ ∈ NmW ω.1 lt) (Q : BH lt) (a : Tω ω.1) (h : interSub H ω.1),
        RH lt (a.1 * h.1) Q ((adapt ω.1 lt).symm ⟨⟨κ, h_lt⟩, Pt₀⟩) =
          ∑ Pt : Bω ω.1 κ, RH lt a.1 Q ((adapt ω.1 lt).symm ⟨⟨κ, h_lt⟩, Pt⟩) *
            Rω ω.1 κ h Pt Pt₀ := by
      intro lt h_lt Q a h
      rw [(hRH.1 lt).1.2 a.1 h.1, Matrix.mul_apply]
      rw [Fintype.sum_equiv (adapt ω.1 lt) _ (fun z =>
        RH lt a.1 Q ((adapt ω.1 lt).symm z) *
          RHad H BH RH Bω NmW adapt ω.1 lt h.1 z ⟨⟨κ, h_lt⟩, Pt₀⟩)
        (fun j => by simp [RHad])]
      rw [Fintype.sum_sigma, Finset.sum_eq_single ⟨κ, h_lt⟩]
      · refine Finset.sum_congr rfl fun Pt _ => ?_
        have had := hAdω ω.1 ω.2 lt h ⟨⟨κ, h_lt⟩, Pt⟩ ⟨⟨κ, h_lt⟩, Pt₀⟩
        rw [dif_pos rfl, cast_eq] at had
        rw [had]
      · intro κ' _ hκ'
        refine Finset.sum_eq_zero fun Pt _ => ?_
        have had := hAdω ω.1 ω.2 lt h ⟨κ', Pt⟩ ⟨⟨κ, h_lt⟩, Pt₀⟩
        simp only [dif_neg hκ'] at had
        rw [had, mul_zero]
      · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
    dsimp [S]
    rw [← Fintype.sum_equiv eT (fun ah =>
      RH lt₁ (ah.1.1 * ah.2.1) Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₀⟩) *
        star (RH lt₂ (ah.1.1 * ah.2.1) Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₀⟩))) _
      (fun ah => rfl)]
    rw [Fintype.sum_prod_type]
    have hcalc :
        ∑ a : Tω ω.1, ∑ h : interSub H ω.1,
          RH lt₁ (a.1 * h.1) Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₀⟩) *
            star (RH lt₂ (a.1 * h.1) Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₀⟩)) =
        ∑ a : Tω ω.1, ∑ Pt₁ : Bω ω.1 κ, ∑ Pt₂ : Bω ω.1 κ,
          RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₁⟩) *
            star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₂⟩)) *
            ∑ h : interSub H ω.1, Rω ω.1 κ h Pt₁ Pt₀ * star (Rω ω.1 κ h Pt₂ Pt₀) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hterm_ah : ∀ h : interSub H ω.1,
          RH lt₁ (a.1 * h.1) Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₀⟩) *
            star (RH lt₂ (a.1 * h.1) Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₀⟩)) =
          ∑ Pt₁ : Bω ω.1 κ, ∑ Pt₂ : Bω ω.1 κ,
            RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₁⟩) *
              star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₂⟩)) *
              (Rω ω.1 κ h Pt₁ Pt₀ * star (Rω ω.1 κ h Pt₂ Pt₀)) := by
        intro h
        rw [h1 lt₁ h₁ Q₁ a h, h1 lt₂ h₂ Q₂ a h]
        simp only [Complex.star_def, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun Pt₁ _ => Finset.sum_congr rfl fun Pt₂ _ => by ring
      simp_rw [hterm_ah]
      calc ∑ h : interSub H ω.1, ∑ Pt₁ : Bω ω.1 κ, ∑ Pt₂ : Bω ω.1 κ,
            RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₁⟩) *
              star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₂⟩)) *
              (Rω ω.1 κ h Pt₁ Pt₀ * star (Rω ω.1 κ h Pt₂ Pt₀))
          = ∑ Pt₁ : Bω ω.1 κ, ∑ h : interSub H ω.1, ∑ Pt₂ : Bω ω.1 κ,
            RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₁⟩) *
              star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₂⟩)) *
              (Rω ω.1 κ h Pt₁ Pt₀ * star (Rω ω.1 κ h Pt₂ Pt₀)) := Finset.sum_comm
        _ = ∑ Pt₁ : Bω ω.1 κ, ∑ Pt₂ : Bω ω.1 κ, ∑ h : interSub H ω.1,
            RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₁⟩) *
              star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ, h₂⟩, Pt₂⟩)) *
              (Rω ω.1 κ h Pt₁ Pt₀ * star (Rω ω.1 κ h Pt₂ Pt₀)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun Pt₁ _ => Finset.sum_congr rfl fun Pt₂ _ => ?_
            rw [Finset.mul_sum]
    rw [hcalc]
    have horth : ∀ Pt₁ Pt₂ : Bω ω.1 κ,
        ∑ h : interSub H ω.1, Rω ω.1 κ h Pt₁ Pt₀ * star (Rω ω.1 κ h Pt₂ Pt₀) =
          ((Fintype.card (interSub H ω.1) : ℂ) / (Fintype.card (Bω ω.1 κ) : ℂ)) *
            (if Pt₁ = Pt₂ then 1 else 0) := by
      intro Pt₁ Pt₂
      rw [schur_orthogonality_eq ((hRω ω.1 ω.2).1 κ) ((hRω ω.1 ω.2).2.1 κ) Pt₁ Pt₀ Pt₂ Pt₀]
      simp
    simp_rw [horth]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Pt₁ _ => ?_
    rw [Finset.sum_eq_single Pt₁]
    · simp only [if_true, mul_one, Complex.star_def]; ring
    · intro Pt₂ _ hPt; simp [hPt.symm]
    · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
  have hS_schur :
      S = if e : lt₁ = lt₂ then
        (if cast (congrArg BH e) Q₁ = Q₂ then
          ((Fintype.card H : ℂ) / (Fintype.card (BH lt₁) : ℂ))
        else 0)
      else 0 := by
    by_cases e : lt₁ = lt₂
    · subst e
      rw [dif_pos rfl, cast_eq]
      dsimp [S]
      have hpt_eq : (adapt ω.1 lt₁).symm ⟨⟨κ, h₁⟩, Pt₀⟩ =
          (adapt ω.1 lt₁).symm ⟨⟨κ, h₂⟩, Pt₀⟩ := rfl
      rw [hpt_eq]
      have hsch := schur_orthogonality_eq (hRH.1 lt₁) (hRH.2.1 lt₁) Q₁
        ((adapt ω.1 lt₁).symm ⟨⟨κ, h₂⟩, Pt₀⟩) Q₂ ((adapt ω.1 lt₁).symm ⟨⟨κ, h₂⟩, Pt₀⟩)
      simp only [Complex.star_def] at hsch
      rw [hsch]
      by_cases hQ : Q₁ = Q₂ <;> simp [hQ]
    · rw [dif_neg e]
      exact schur_orthogonality_ne (hRH.1 lt₂) (hRH.1 lt₁) (hRH.2.1 lt₂) (hRH.2.1 lt₁)
        (hRH.2.2.1 lt₂ lt₁ (Ne.symm e)) _ _ _ _
  have hH_card : Fintype.card H = Fintype.card (Tω ω.1) * Fintype.card (interSub H ω.1) := by
    rw [← Fintype.card_prod, Fintype.card_congr eT]
  have hI_ne : (Fintype.card (interSub H ω.1) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hK_ne : (Fintype.card (Bω ω.1 κ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcoeff_ne : ((Fintype.card (interSub H ω.1) : ℂ) / (Fintype.card (Bω ω.1 κ) : ℂ)) ≠ 0 :=
    div_ne_zero hI_ne hK_ne
  have heq_mul := hS_split.symm.trans hS_schur
  apply mul_left_cancel₀ hcoeff_ne
  rw [heq_mul]
  by_cases e : lt₁ = lt₂
  · subst e
    by_cases hQ : Q₁ = Q₂
    · subst hQ
      simp only [cast_eq, if_true]
      rw [hH_card]
      push_cast
      field_simp
    · simp [hQ]
  · simp [e]

private theorem uind_mul_nop_conjTranspose {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (Ω : Set G) (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (NmW : ∀ ω, ΛH → Finset (Λω ω)) (adapt : ∀ ω l, BH l ≃ AdBas (Bω ω) (NmW ω) l)
    (hAdω : ∀ ω ∈ Ω, IsAdaptedToInter H BH RH Bω Rω NmW adapt ω)
    (Ntw : ∀ ω, ΛH → Finset (Λω ω)) (Utw : ∀ ω l, Matrix (Σ κ : Ntw ω l, Bω ω κ.1) (BH l) ℂ)
    (hUtw : ∀ ω ∈ Ω, ∀ l, IsUntwisting H BH RH Bω Rω Ntw Utw ω l) (l : ΛH) :
    UIndLam (mackeyT H Ω Tω) BH Nminus RG l *
        (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ =
      Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l := by
  let eM := mackeyT_equiv H Ω hΩ Tω hTω
  have hT_comp := mackeyT_isComplement H Ω hΩ Tω hTω
  have hcard_T : Fintype.card (mackeyT H Ω Tω) = H.index :=
    card_complement_eq_index H (mackeyT H Ω Tω) hT_comp
  ext out o
  rcases out with ⟨⟨μ, hμ_l⟩, ⟨⟨lt₁, hμ_lt1⟩, Q₁⟩⟩
  rcases o with ⟨ω, κ, ⟨lt₂, hκ_lt2⟩, Q₂⟩
  have hcard_Tω : Fintype.card (Tω ω.1) = (interSub H ω.1).index :=
    card_complement_eq_index (interSub H ω.1) (Tω ω.1) (hTω ω.1 ω.2)
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Fintype.sum_equiv eM.symm _ (fun x => ∑ P : BH l,
    UIndLam (mackeyT H Ω Tω) BH Nminus RG l ⟨⟨μ, hμ_l⟩, ⟨⟨lt₁, hμ_lt1⟩, Q₁⟩⟩ (eM x, P) *
      (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ (eM x, P) ⟨ω, κ, ⟨lt₂, hκ_lt2⟩, Q₂⟩)
    (fun t => by simp [eM.apply_symm_apply])]
  rw [Fintype.sum_sigma, Finset.sum_eq_single ω]
  · have hnop_eval : ∀ (a : Tω ω.1) (P : BH l),
        (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ (eM ⟨ω, a⟩, P) ⟨ω, κ, ⟨lt₂, hκ_lt2⟩, Q₂⟩ =
          star (∑ Pt : Bω ω.1 κ.1,
            UIndLam (Tω ω.1) (Bω ω.1) (NmW ω.1) (RHad H BH RH Bω NmW adapt ω.1) κ.1
              ⟨⟨lt₂, hκ_lt2⟩, adapt ω.1 lt₂ Q₂⟩ (a, Pt) * Utw ω.1 l ⟨κ, Pt⟩ P) := by
      intro a P
      rw [Matrix.conjTranspose_apply, nop_apply_mackeyT ⟨ω, κ, ⟨lt₂, hκ_lt2⟩, Q₂⟩ ω a P, dif_pos rfl]
    simp_rw [hnop_eval]
    let c₁ : ℝ := Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
      ((Fintype.card (BH l) : ℝ) * (Fintype.card (mackeyT H Ω Tω) : ℝ)))
    let c₂ : ℝ := Real.sqrt ((Fintype.card (BH lt₂) : ℝ) /
      ((Fintype.card (Bω ω.1 κ.1) : ℝ) * (Fintype.card (Tω ω.1) : ℝ)))
    let M : Matrix (BH lt₁) (Bω ω.1 κ.1) ℂ := Matrix.of fun R Pt =>
      ∑ P : BH l, RG μ (ω : G) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P⟩ * conj (Utw ω.1 l ⟨κ, Pt⟩ P)
    have hM_inter : ∀ h : interSub H ω.1, RH lt₁ h.1 * M = M * Rω ω.1 κ.1 h := by
      intro h
      ext R Pt
      simp only [Matrix.mul_apply, M, Matrix.of_apply]
      have hLHS :
          ∑ R' : BH lt₁, RH lt₁ h.1 R R' *
            ∑ P : BH l, RG μ (ω : G) ⟨⟨lt₁, hμ_lt1⟩, R'⟩ ⟨⟨l, hμ_l⟩, P⟩ *
              conj (Utw ω.1 l ⟨κ, Pt⟩ P) =
          ∑ P : BH l, RG μ ((h.1 : G) * (ω : G)) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P⟩ *
            conj (Utw ω.1 l ⟨κ, Pt⟩ P) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun P _ => ?_
        simp only [← mul_assoc]
        rw [← Finset.sum_mul]
        congr 1
        have hstep : RG μ ((h.1 : G) * (ω : G)) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P⟩ =
            ∑ R' : BH lt₁, RH lt₁ h.1 R R' * RG μ (ω : G) ⟨⟨lt₁, hμ_lt1⟩, R'⟩ ⟨⟨l, hμ_l⟩, P⟩ := by
          rw [(hRG.1 μ).1.2 (h.1 : G) (ω : G), Matrix.mul_apply, Fintype.sum_sigma,
            Finset.sum_eq_single ⟨lt₁, hμ_lt1⟩]
          · refine Finset.sum_congr rfl fun R' _ => ?_
            have had := hAd μ h.1 ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨lt₁, hμ_lt1⟩, R'⟩
            rw [dif_pos rfl, cast_eq] at had
            rw [had]
          · intro lt' _ hlt'
            refine Finset.sum_eq_zero fun R' _ => ?_
            have had := hAd μ h.1 ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨lt', R'⟩
            simp only [dif_neg (Ne.symm hlt')] at had
            rw [had, zero_mul]
          · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
        rw [hstep]
      let h' : H := ⟨(ω : G)⁻¹ * (h.1 : G) * (ω : G), interSub_conj_mem H ω.1 h⟩
      have hhw : (h.1 : G) * (ω : G) = (ω : G) * (h' : G) := by simp [h', mul_assoc]
      rw [hLHS]
      have hRHS_expand :
          ∑ P : BH l, RG μ ((h.1 : G) * (ω : G)) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P⟩ *
            conj (Utw ω.1 l ⟨κ, Pt⟩ P) =
          ∑ P' : BH l, RG μ (ω : G) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P'⟩ *
            ∑ P : BH l, twistRep H ω.1 (RH l) h P' P * conj (Utw ω.1 l ⟨κ, Pt⟩ P) := by
        have hstep : ∀ P : BH l,
            RG μ ((h.1 : G) * (ω : G)) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P⟩ =
              ∑ P' : BH l, RG μ (ω : G) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P'⟩ *
                twistRep H ω.1 (RH l) h P' P := by
          intro P
          rw [hhw, (hRG.1 μ).1.2 (ω : G) (h' : G), Matrix.mul_apply, Fintype.sum_sigma,
            Finset.sum_eq_single ⟨l, hμ_l⟩]
          · refine Finset.sum_congr rfl fun P' _ => ?_
            have had := hAd μ h' ⟨⟨l, hμ_l⟩, P'⟩ ⟨⟨l, hμ_l⟩, P⟩
            rw [dif_pos rfl, cast_eq] at had
            rw [had]
            rfl
          · intro l' _ hl'
            refine Finset.sum_eq_zero fun P' _ => ?_
            have had := hAd μ h' ⟨l', P'⟩ ⟨⟨l, hμ_l⟩, P⟩
            simp only [dif_neg hl'] at had
            rw [had, mul_zero]
          · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
        simp_rw [hstep, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun P' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun P _ => by ring
      rw [hRHS_expand]
      simp_rw [twistRep_mul_conjTranspose_utw H ω.1 BH RH Bω Rω Ntw Utw l (hUtw ω.1 ω.2 l) h _ κ Pt]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun Pt' _ => ?_
      simp only [← mul_assoc]
      rw [← Finset.sum_mul]
    have hMblock : ∀ (κ' : NmW ω.1 lt₁) (h : interSub H ω.1),
        Rω ω.1 κ'.1 h * Matrix.of (fun (Pt' : Bω ω.1 κ'.1) (Pt : Bω ω.1 κ.1) =>
          M ((adapt ω.1 lt₁).symm ⟨κ', Pt'⟩) Pt) =
        Matrix.of (fun (Pt' : Bω ω.1 κ'.1) (Pt : Bω ω.1 κ.1) =>
          M ((adapt ω.1 lt₁).symm ⟨κ', Pt'⟩) Pt) * Rω ω.1 κ.1 h := by
      intro κ' h
      ext Pt' Pt
      have hentry := congr_fun (congr_fun (hM_inter h) ((adapt ω.1 lt₁).symm ⟨κ', Pt'⟩)) Pt
      simp only [Matrix.mul_apply, Matrix.of_apply] at hentry ⊢
      have hlhs :
          ∑ x : BH lt₁, RH lt₁ h.1 ((adapt ω.1 lt₁).symm ⟨κ', Pt'⟩) x * M x Pt =
            ∑ Pt'' : Bω ω.1 κ'.1, Rω ω.1 κ'.1 h Pt' Pt'' * M ((adapt ω.1 lt₁).symm ⟨κ', Pt''⟩) Pt := by
        rw [Fintype.sum_equiv (adapt ω.1 lt₁) _ (fun z =>
          RHad H BH RH Bω NmW adapt ω.1 lt₁ h.1 ⟨κ', Pt'⟩ z * M ((adapt ω.1 lt₁).symm z) Pt)
          (fun x => by simp [RHad])]
        rw [Fintype.sum_sigma, Finset.sum_eq_single κ']
        · refine Finset.sum_congr rfl fun Pt'' _ => ?_
          have had := hAdω ω.1 ω.2 lt₁ h ⟨κ', Pt'⟩ ⟨κ', Pt''⟩
          rw [dif_pos rfl, cast_eq] at had
          rw [had]
        · intro κ'' _ hκ''
          refine Finset.sum_eq_zero fun Pt'' _ => ?_
          have had := hAdω ω.1 ω.2 lt₁ h ⟨κ', Pt'⟩ ⟨κ'', Pt''⟩
          simp only [dif_neg (Ne.symm hκ'')] at had
          rw [had, zero_mul]
        · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
      rw [← hlhs, hentry]
    have hsum_expand :
        ∑ a : Tω ω.1, ∑ P : BH l,
          UIndLam (mackeyT H Ω Tω) BH Nminus RG l ⟨⟨μ, hμ_l⟩, ⟨⟨lt₁, hμ_lt1⟩, Q₁⟩⟩
            (eM ⟨ω, a⟩, P) *
          star (∑ Pt : Bω ω.1 κ.1,
            UIndLam (Tω ω.1) (Bω ω.1) (NmW ω.1) (RHad H BH RH Bω NmW adapt ω.1) κ.1
              ⟨⟨lt₂, hκ_lt2⟩, adapt ω.1 lt₂ Q₂⟩ (a, Pt) *
            Utw ω.1 l ⟨κ, Pt⟩ P) =
        (c₁ : ℂ) * (c₂ : ℂ) *
          ∑ a : Tω ω.1, ∑ R : BH lt₁, ∑ Pt : Bω ω.1 κ.1,
            (RH lt₁ a.1 Q₁ R *
              star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩))) * M R Pt := by
      have hterm : ∀ (a : Tω ω.1) (P : BH l),
          UIndLam (mackeyT H Ω Tω) BH Nminus RG l ⟨⟨μ, hμ_l⟩, ⟨⟨lt₁, hμ_lt1⟩, Q₁⟩⟩
            (eM ⟨ω, a⟩, P) *
          star (∑ Pt : Bω ω.1 κ.1,
            UIndLam (Tω ω.1) (Bω ω.1) (NmW ω.1) (RHad H BH RH Bω NmW adapt ω.1) κ.1
              ⟨⟨lt₂, hκ_lt2⟩, adapt ω.1 lt₂ Q₂⟩ (a, Pt) *
            Utw ω.1 l ⟨κ, Pt⟩ P) =
          (c₁ : ℂ) * (c₂ : ℂ) *
            ∑ R : BH lt₁, ∑ Pt : Bω ω.1 κ.1,
              (RH lt₁ a.1 Q₁ R *
                star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩))) *
              (RG μ (ω : G) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P⟩ * conj (Utw ω.1 l ⟨κ, Pt⟩ P)) := by
        intro a P
        simp only [UIndLam, Matrix.of_apply]
        have hRG_aw : RG μ (eM ⟨ω, a⟩ : G) ⟨⟨lt₁, hμ_lt1⟩, Q₁⟩ ⟨⟨l, hμ_l⟩, P⟩ =
            ∑ R : BH lt₁, RH lt₁ a.1 Q₁ R * RG μ (ω : G) ⟨⟨lt₁, hμ_lt1⟩, R⟩ ⟨⟨l, hμ_l⟩, P⟩ := by
          change RG μ ((a.1 : G) * (ω : G)) ⟨⟨lt₁, hμ_lt1⟩, Q₁⟩ ⟨⟨l, hμ_l⟩, P⟩ = _
          rw [(hRG.1 μ).1.2 (a.1 : G) (ω : G), Matrix.mul_apply, Fintype.sum_sigma,
            Finset.sum_eq_single ⟨lt₁, hμ_lt1⟩]
          · refine Finset.sum_congr rfl fun R _ => ?_
            have had := hAd μ a.1 ⟨⟨lt₁, hμ_lt1⟩, Q₁⟩ ⟨⟨lt₁, hμ_lt1⟩, R⟩
            rw [dif_pos rfl, cast_eq] at had
            rw [had]
          · intro lt' _ hlt'
            refine Finset.sum_eq_zero fun R _ => ?_
            have had := hAd μ a.1 ⟨⟨lt₁, hμ_lt1⟩, Q₁⟩ ⟨lt', R⟩
            simp only [dif_neg (Ne.symm hlt')] at had
            rw [had, zero_mul]
          · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
        have hRHad_a : ∀ Pt : Bω ω.1 κ.1,
            RHad H BH RH Bω NmW adapt ω.1 lt₂ a.1 (adapt ω.1 lt₂ Q₂) ⟨⟨κ.1, hκ_lt2⟩, Pt⟩ =
              RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩) := by
          intro Pt; simp [RHad]
        rw [hRG_aw]
        simp_rw [hRHad_a]
        simp only [Complex.star_def, map_sum, map_mul, Complex.conj_ofReal,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        have hcard_ad : Fintype.card (AdBas (Bω ω.1) (NmW ω.1) lt₂) = Fintype.card (BH lt₂) :=
          (Fintype.card_congr (adapt ω.1 lt₂)).symm
        refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun Pt _ => ?_
        simp only [c₁, c₂, hcard_ad]
        ring
      simp_rw [hterm, ← Finset.mul_sum]
      refine congrArg ((c₁ : ℂ) * (c₂ : ℂ) * ·) ?_
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun R _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun Pt _ => ?_
      simp only [M, Matrix.of_apply, Finset.mul_sum]
    rw [hsum_expand]
    by_cases hκ_mem : κ.1 ∈ NmW ω.1 lt₁
    · let pathSum : ℂ := ∑ P : BH l, ∑ Pt : Bω ω.1 κ.1,
        RG μ (ω : G) ⟨⟨lt₁, hμ_lt1⟩, (adapt ω.1 lt₁).symm ⟨⟨κ.1, hκ_mem⟩, Pt⟩⟩ ⟨⟨l, hμ_l⟩, P⟩ *
          conj (Utw ω.1 l ⟨κ, Pt⟩ P)
      let Mdiag : Matrix (Bω ω.1 κ.1) (Bω ω.1 κ.1) ℂ :=
        Matrix.of fun Pt' Pt => M ((adapt ω.1 lt₁).symm ⟨⟨κ.1, hκ_mem⟩, Pt'⟩) Pt
      obtain ⟨c, hc⟩ := schur_eq_smul_one ((hRω ω.1 ω.2).2.1 κ.1) (hMblock ⟨κ.1, hκ_mem⟩)
      have hc_val : c = pathSum / (Fintype.card (Bω ω.1 κ.1) : ℂ) := by
        have htr : Mdiag.trace = (c • (1 : Matrix (Bω ω.1 κ.1) (Bω ω.1 κ.1) ℂ)).trace :=
          congrArg Matrix.trace hc
        rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at htr
        have htr_path : Mdiag.trace = pathSum := by
          simp only [Mdiag, Matrix.trace, Matrix.diag, Matrix.of_apply, M, pathSum]
          rw [Finset.sum_comm]
        rw [htr_path] at htr
        have hdκ : (Fintype.card (Bω ω.1 κ.1) : ℂ) ≠ 0 := by
          have : Nonempty (Bω ω.1 κ.1) := ((hRω ω.1 ω.2).2.1 κ.1).1
          exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        exact eq_div_of_mul_eq hdκ htr.symm
      have hM_reidx :
          ∑ a : Tω ω.1, ∑ R : BH lt₁, ∑ Pt : Bω ω.1 κ.1,
            (RH lt₁ a.1 Q₁ R *
              star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩))) * M R Pt =
          (pathSum / (Fintype.card (Bω ω.1 κ.1) : ℂ)) *
            ∑ a : Tω ω.1, ∑ Pt : Bω ω.1 κ.1,
              RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ.1, hκ_mem⟩, Pt⟩) *
                star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩)) := by
        have hinner : ∀ a : Tω ω.1,
            ∑ R : BH lt₁, ∑ Pt : Bω ω.1 κ.1,
              (RH lt₁ a.1 Q₁ R *
                star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩))) * M R Pt =
            (pathSum / (Fintype.card (Bω ω.1 κ.1) : ℂ)) *
              ∑ Pt : Bω ω.1 κ.1,
                RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm ⟨⟨κ.1, hκ_mem⟩, Pt⟩) *
                  star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩)) := by
          intro a
          rw [Fintype.sum_equiv (adapt ω.1 lt₁) _ (fun z => ∑ Pt : Bω ω.1 κ.1,
            (RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm z) *
              star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩))) *
              M ((adapt ω.1 lt₁).symm z) Pt) (fun _ => by simp)]
          rw [Fintype.sum_sigma, Finset.sum_eq_single ⟨κ.1, hκ_mem⟩]
          · rw [Finset.sum_comm, Finset.mul_sum]
            refine Finset.sum_congr rfl fun Pt _ => ?_
            rw [Finset.sum_eq_single Pt]
            · have hdiag : Mdiag Pt Pt = c := by
                dsimp only [Mdiag]
                rw [hc]; simp
              have hdiag' : M ((adapt ω.1 lt₁).symm ⟨⟨κ.1, hκ_mem⟩, Pt⟩) Pt =
                  pathSum / (Fintype.card (Bω ω.1 κ.1) : ℂ) := by
                simpa [Mdiag] using hdiag.trans hc_val
              rw [hdiag']; ring
            · intro Pt' _ hPt'
              have hne : Mdiag Pt' Pt = 0 := by
                dsimp only [Mdiag]
                rw [hc]; simp [hPt']
              have hne' : M ((adapt ω.1 lt₁).symm ⟨⟨κ.1, hκ_mem⟩, Pt'⟩) Pt = 0 := by
                simpa [Mdiag] using hne
              rw [hne', mul_zero]
            · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
          · intro κ' _ hκ'
            refine Finset.sum_eq_zero fun Pt' _ => Finset.sum_eq_zero fun Pt _ => ?_
            have hne_val : κ'.1 ≠ κ.1 := fun h => hκ' (Subtype.ext h)
            have hzero_mat :
                Matrix.of (fun (Pt' : Bω ω.1 κ'.1) (Pt : Bω ω.1 κ.1) =>
                  M ((adapt ω.1 lt₁).symm ⟨κ', Pt'⟩) Pt) = 0 :=
              schur_zero_of_not_repEquiv ((hRω ω.1 ω.2).2.1 κ.1) ((hRω ω.1 ω.2).2.1 κ'.1)
                ((hRω ω.1 ω.2).2.2.1 κ.1 κ'.1 (Ne.symm hne_val)) (hMblock κ')
            have hzero_entry := congr_fun (congr_fun hzero_mat Pt') Pt
            simp only [Matrix.of_apply, Matrix.zero_apply] at hzero_entry
            rw [hzero_entry, mul_zero]
          · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
        simp_rw [hinner, ← Finset.mul_sum]
      rw [hM_reidx, sum_Tω_RH_mul_conj H Ω Tω hTω BH RH hRH Bω Rω hRω NmW adapt hAdω ω κ.1 lt₁ lt₂
        hκ_mem hκ_lt2 Q₁ Q₂]
      simp only [Aop, Matrix.of_apply]
      by_cases e : lt₁ = lt₂
      · subst e
        rw [dif_pos rfl, dif_pos rfl]
        simp only [cast_eq]
        by_cases hQ : Q₁ = Q₂
        · subst hQ
          simp only [if_true]
          simp only [Ablock, Matrix.of_apply]
          have hI_pos : (0 : ℝ) < (interSub H ω.1).index :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          have hH_pos : (0 : ℝ) < H.index :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          have : Nonempty (Bω ω.1 κ.1) := ((hRω ω.1 ω.2).2.1 κ.1).1
          have : Nonempty (BH lt₁) := (hRH.2.1 lt₁).1
          have : Nonempty (BH l) := (hRH.2.1 l).1
          have dK_pos : (0 : ℝ) < Fintype.card (Bω ω.1 κ.1) := Nat.cast_pos.mpr Fintype.card_pos
          have dLt_pos : (0 : ℝ) < Fintype.card (BH lt₁) := Nat.cast_pos.mpr Fintype.card_pos
          have dL_pos : (0 : ℝ) < Fintype.card (BH l) := Nat.cast_pos.mpr Fintype.card_pos
          have hsqrt :
              (c₁ : ℂ) * (c₂ : ℂ) *
                ((pathSum / (Fintype.card (Bω ω.1 κ.1) : ℂ)) *
                  (((Fintype.card (Tω ω.1) : ℂ) * (Fintype.card (Bω ω.1 κ.1) : ℂ)) /
                    (Fintype.card (BH lt₁) : ℂ))) =
              (Real.sqrt (((Fintype.card (AdBas BH Nminus μ) : ℝ) *
                  ((interSub H ω.1).index : ℝ)) /
                ((Fintype.card (Bω ω.1 κ.1) : ℝ) * (Fintype.card (BH l) : ℝ) *
                  (Fintype.card (BH lt₁) : ℝ) * (H.index : ℝ))) : ℂ) * pathSum := by
            have hdκ_ne : (Fintype.card (Bω ω.1 κ.1) : ℂ) ≠ 0 := by exact_mod_cast dK_pos.ne'
            have hscalar :
                (c₁ : ℂ) * (c₂ : ℂ) * ((Fintype.card (Tω ω.1) : ℂ) / (Fintype.card (BH lt₁) : ℂ)) =
                  (Real.sqrt (((Fintype.card (AdBas BH Nminus μ) : ℝ) *
                    ((interSub H ω.1).index : ℝ)) /
                  ((Fintype.card (Bω ω.1 κ.1) : ℝ) * (Fintype.card (BH l) : ℝ) *
                    (Fintype.card (BH lt₁) : ℝ) * (H.index : ℝ))) : ℂ) := by
              have hr :
                  c₁ * c₂ * ((Fintype.card (Tω ω.1) : ℝ) / (Fintype.card (BH lt₁) : ℝ)) =
                    Real.sqrt (((Fintype.card (AdBas BH Nminus μ) : ℝ) *
                      ((interSub H ω.1).index : ℝ)) /
                    ((Fintype.card (Bω ω.1 κ.1) : ℝ) * (Fintype.card (BH l) : ℝ) *
                      (Fintype.card (BH lt₁) : ℝ) * (H.index : ℝ))) := by
                dsimp [c₁, c₂]
                rw [hcard_T, hcard_Tω]
                have hpos_frac : 0 ≤ ((interSub H ω.1).index : ℝ) / (Fintype.card (BH lt₁) : ℝ) := by
                  positivity
                rw [← Real.sqrt_sq hpos_frac]
                rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
                congr 1
                field_simp
              have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
              simpa using hc
            calc (c₁ : ℂ) * (c₂ : ℂ) *
                  ((pathSum / (Fintype.card (Bω ω.1 κ.1) : ℂ)) *
                    (((Fintype.card (Tω ω.1) : ℂ) * (Fintype.card (Bω ω.1 κ.1) : ℂ)) /
                      (Fintype.card (BH lt₁) : ℂ)))
                = ((c₁ : ℂ) * (c₂ : ℂ) *
                    ((Fintype.card (Tω ω.1) : ℂ) / (Fintype.card (BH lt₁) : ℂ))) * pathSum := by
                  field_simp [hdκ_ne]
              _ = _ := by rw [hscalar]
          rw [hsqrt]
        · simp [hQ]
      · simp [e]
    · have hzero :
          ∑ a : Tω ω.1, ∑ R : BH lt₁, ∑ Pt : Bω ω.1 κ.1,
            (RH lt₁ a.1 Q₁ R *
              star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩))) * M R Pt = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        rw [Fintype.sum_equiv (adapt ω.1 lt₁) _ (fun z => ∑ Pt : Bω ω.1 κ.1,
          (RH lt₁ a.1 Q₁ ((adapt ω.1 lt₁).symm z) *
            star (RH lt₂ a.1 Q₂ ((adapt ω.1 lt₂).symm ⟨⟨κ.1, hκ_lt2⟩, Pt⟩))) *
            M ((adapt ω.1 lt₁).symm z) Pt) (fun _ => by simp)]
        refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun Pt _ => ?_
        have hne_val : z.1.1 ≠ κ.1 := fun h => hκ_mem (h ▸ z.1.2)
        have hzero_mat :
            Matrix.of (fun (Pt' : Bω ω.1 z.1.1) (Pt : Bω ω.1 κ.1) =>
              M ((adapt ω.1 lt₁).symm ⟨z.1, Pt'⟩) Pt) = 0 :=
          schur_zero_of_not_repEquiv ((hRω ω.1 ω.2).2.1 κ.1) ((hRω ω.1 ω.2).2.1 z.1.1)
            ((hRω ω.1 ω.2).2.2.1 κ.1 z.1.1 (Ne.symm hne_val)) (hMblock z.1)
        have hzero_entry := congr_fun (congr_fun hzero_mat z.2) Pt
        simp only [Matrix.of_apply, Matrix.zero_apply] at hzero_entry
        rw [hzero_entry, mul_zero]
      have hne_lt : lt₁ ≠ lt₂ := fun h => hκ_mem (h ▸ hκ_lt2)
      rw [hzero, mul_zero]
      simp [Aop, hne_lt]
  · intro ω' _ hω'
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun P _ => ?_
    rw [Matrix.conjTranspose_apply, nop_apply_mackeyT ⟨ω, κ, ⟨lt₂, hκ_lt2⟩, Q₂⟩ ω' a P,
      dif_neg (Ne.symm hω'), star_zero, mul_zero]
  · intro hmem; exact False.elim (hmem (Finset.mem_univ _))

private theorem sum_dite_eq_sum_subtype {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    [Fintype {a : α // P a}] (f : {a : α // P a} → ℂ) :
    (∑ a : α, if h : P a then f ⟨a, h⟩ else 0) = ∑ a : {a : α // P a}, f a := by
  have h1 : (∑ a : α, if h : P a then f ⟨a, h⟩ else 0) =
      ∑ a ∈ Finset.univ.filter P, if h : P a then f ⟨a, h⟩ else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> rfl
  rw [h1]
  have h2 : (∑ a ∈ Finset.univ.filter P, if h : P a then f ⟨a, h⟩ else 0) =
      ∑ a : (Finset.univ.filter P), f ⟨a.1, (Finset.mem_filter.mp a.2).2⟩ := by
    rw [← Finset.sum_coe_sort (Finset.univ.filter P)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dif_pos (Finset.mem_filter.mp a.2).2]
  rw [h2]
  let e : (Finset.univ.filter P) ≃ {a : α // P a} :=
    { toFun := fun a => ⟨a.1, (Finset.mem_filter.mp a.2).2⟩
      invFun := fun a => ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GL2QFT.Supplement.MackeyProof

open GL2QFT.Supplement.MackeyProof in
theorem solution {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type) [∀ ω κ, Fintype (Bω ω κ)]
    [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (NmW : ∀ ω, ΛH → Finset (Λω ω)) (adapt : ∀ ω l, BH l ≃ AdBas (Bω ω) (NmW ω) l)
    (hAdω : ∀ ω ∈ Ω, IsAdaptedToInter H BH RH Bω Rω NmW adapt ω)
    (Ntw : ∀ ω, ΛH → Finset (Λω ω)) (Utw : ∀ ω l, Matrix (Σ κ : Ntw ω l, Bω ω κ.1) (BH l) ℂ)
    (hUtw : ∀ ω ∈ Ω, ∀ l, IsUntwisting H BH RH Bω Rω Ntw Utw ω l) (l : ΛH) :
    Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l * Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l =
        UIndLam (mackeyT H Ω Tω) BH Nminus RG l ∧
      ∀ lt : ΛH,
        Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt *
            (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt)ᴴ = 1 ∧
          (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt)ᴴ *
            Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt = 1 := by
  have hT_comp := mackeyT_isComplement H Ω hΩ Tω hTω
  have hU_unit := uindLam_unitary H (mackeyT H Ω Tω) hT_comp BH Nminus RH hRH RG hRG hAd l
  have hN_unit := nop_unitary H Ω hΩ Tω hTω BH RH hRH Bω Rω hRω NmW adapt hAdω Ntw Utw hUtw l
  have hA_eq : Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l =
      UIndLam (mackeyT H Ω Tω) BH Nminus RG l *
        (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ :=
    (uind_mul_nop_conjTranspose H Ω hΩ Tω hTω BH Nminus RH hRH RG hRG hAd Bω Rω hRω
      NmW adapt hAdω Ntw Utw hUtw l).symm
  have hAN : Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l *
      Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l =
      UIndLam (mackeyT H Ω Tω) BH Nminus RG l := by
    calc Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l *
          Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l
        = (UIndLam (mackeyT H Ω Tω) BH Nminus RG l *
            (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ) *
            Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l := by rw [hA_eq]
      _ = UIndLam (mackeyT H Ω Tω) BH Nminus RG l *
            ((Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ *
              Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l) := Matrix.mul_assoc _ _ _
      _ = UIndLam (mackeyT H Ω Tω) BH Nminus RG l := by rw [hN_unit.2, Matrix.mul_one]
  have hAA_mul :
      Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l *
        (Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l)ᴴ = 1 := by
    calc Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l *
          (Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l)ᴴ
        = (UIndLam (mackeyT H Ω Tω) BH Nminus RG l *
            (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ) *
            (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l *
              (UIndLam (mackeyT H Ω Tω) BH Nminus RG l)ᴴ) := by
          rw [hA_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = UIndLam (mackeyT H Ω Tω) BH Nminus RG l *
            ((Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ *
              Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l) *
            (UIndLam (mackeyT H Ω Tω) BH Nminus RG l)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = UIndLam (mackeyT H Ω Tω) BH Nminus RG l *
            (UIndLam (mackeyT H Ω Tω) BH Nminus RG l)ᴴ := by
          rw [hN_unit.2, Matrix.mul_one]
      _ = 1 := hU_unit.2
  have hAA_conj :
      (Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l)ᴴ *
        Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l = 1 := by
    calc (Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l)ᴴ *
          Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l
        = (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l *
            (UIndLam (mackeyT H Ω Tω) BH Nminus RG l)ᴴ) *
            (UIndLam (mackeyT H Ω Tω) BH Nminus RG l *
              (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ) := by
          rw [hA_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l *
            ((UIndLam (mackeyT H Ω Tω) BH Nminus RG l)ᴴ *
              UIndLam (mackeyT H Ω Tω) BH Nminus RG l) *
            (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l *
            (Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l)ᴴ := by
          rw [hU_unit.1, Matrix.mul_one]
      _ = 1 := hN_unit.1
  refine ⟨hAN, fun lt => ?_⟩
  have : Nonempty (BH lt) := (hRH.2.1 lt).1
  obtain ⟨Q₀⟩ := ‹Nonempty (BH lt)›
  constructor
  · ext μ₁ μ₂
    have hentry := congr_fun (congr_fun hAA_mul
      ⟨⟨μ₁.1, μ₁.2.1⟩, ⟨⟨lt, μ₁.2.2⟩, Q₀⟩⟩) ⟨⟨μ₂.1, μ₂.2.1⟩, ⟨⟨lt, μ₂.2.2⟩, Q₀⟩⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry ⊢
    have hred :
        ∑ o : NOut Ω BH NmW Ntw (Λω := Λω) l,
          Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l
            ⟨⟨μ₁.1, μ₁.2.1⟩, ⟨⟨lt, μ₁.2.2⟩, Q₀⟩⟩ o *
          star (Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l
            ⟨⟨μ₂.1, μ₂.2.1⟩, ⟨⟨lt, μ₂.2.2⟩, Q₀⟩⟩ o) =
        ∑ ωκ : KSet Ω NmW Ntw (Λω := Λω) l lt,
          Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ₁ ωκ *
            star (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ₂ ωκ) := by
      rw [Fintype.sum_sigma, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Fintype.sum_sigma]
      have hκ_step : ∀ κ : Ntw ω.1 l,
          ∑ x : (Σ lt' : {lt' : ΛH // κ.1 ∈ NmW ω.1 lt'}, BH lt'.1),
            Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l
              ⟨⟨μ₁.1, μ₁.2.1⟩, ⟨⟨lt, μ₁.2.2⟩, Q₀⟩⟩ ⟨ω, κ, x⟩ *
            star (Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l
              ⟨⟨μ₂.1, μ₂.2.1⟩, ⟨⟨lt, μ₂.2.2⟩, Q₀⟩⟩ ⟨ω, κ, x⟩) =
          if hκ : κ.1 ∈ NmW ω.1 lt then
            Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ₁ ⟨ω, ⟨κ.1, κ.2, hκ⟩⟩ *
              star (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ₂ ⟨ω, ⟨κ.1, κ.2, hκ⟩⟩)
          else 0 := by
        intro κ
        rw [Fintype.sum_sigma]
        by_cases hκ : κ.1 ∈ NmW ω.1 lt
        · rw [dif_pos hκ, Finset.sum_eq_single ⟨lt, hκ⟩]
          · rw [Finset.sum_eq_single Q₀]
            · simp [Aop]
            · intro Q' _ hQ'
              simp [Aop, hQ'.symm]
            · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
          · intro lt' _ hlt'
            refine Finset.sum_eq_zero fun Q' _ => ?_
            have hne : lt ≠ lt'.1 := fun h => hlt' (Subtype.ext h.symm)
            simp [Aop, hne]
          · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
        · rw [dif_neg hκ]
          refine Finset.sum_eq_zero fun lt' _ => Finset.sum_eq_zero fun Q' _ => ?_
          have hne : lt ≠ lt'.1 := fun h => hκ (h ▸ lt'.2)
          simp [Aop, hne]
      simp_rw [hκ_step]
      trans ∑ κ : {κ : Ntw ω.1 l // κ.1 ∈ NmW ω.1 lt},
          Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ₁ ⟨ω, ⟨κ.1.1, κ.1.2, κ.2⟩⟩ *
            star (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ₂ ⟨ω, ⟨κ.1.1, κ.1.2, κ.2⟩⟩)
      · convert sum_dite_eq_sum_subtype (fun κ : Ntw ω.1 l => κ.1 ∈ NmW ω.1 lt)
          (fun κ =>
            Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ₁ ⟨ω, ⟨κ.1.1, κ.1.2, κ.2⟩⟩ *
              star (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ₂ ⟨ω, ⟨κ.1.1, κ.1.2, κ.2⟩⟩))
      · let eK : {κ : Ntw ω.1 l // κ.1 ∈ NmW ω.1 lt} ≃
            {κ : Λω ω.1 // κ ∈ Ntw ω.1 l ∧ κ ∈ NmW ω.1 lt} :=
          { toFun := fun κ => ⟨κ.1.1, κ.1.2, κ.2⟩
            invFun := fun κ => ⟨⟨κ.1, κ.2.1⟩, κ.2.2⟩
            left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
            right_inv := fun ⟨_, _, _⟩ => rfl }
        exact Fintype.sum_equiv eK _ _ fun _ => rfl
    rw [← hred, hentry]
    have heq : (⟨⟨μ₁.1, μ₁.2.1⟩, ⟨⟨lt, μ₁.2.2⟩, Q₀⟩⟩ :
          Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1) =
        ⟨⟨μ₂.1, μ₂.2.1⟩, ⟨⟨lt, μ₂.2.2⟩, Q₀⟩⟩ ↔ μ₁ = μ₂ := by
      constructor
      · intro h
        exact Subtype.ext (congrArg (fun x => x.1.1) h)
      · intro h
        rcases μ₁ with ⟨μ₁v, h1a, h1b⟩
        rcases μ₂ with ⟨μ₂v, h2a, h2b⟩
        have hv : μ₁v = μ₂v := congrArg Subtype.val h
        subst hv
        rfl
    exact if_congr heq rfl rfl
  · ext ωκ₁ ωκ₂
    let o₁ : NOut Ω BH NmW Ntw (Λω := Λω) l := ⟨ωκ₁.1, ⟨ωκ₁.2.1, ωκ₁.2.2.1⟩, ⟨lt, ωκ₁.2.2.2⟩, Q₀⟩
    let o₂ : NOut Ω BH NmW Ntw (Λω := Λω) l := ⟨ωκ₂.1, ⟨ωκ₂.2.1, ωκ₂.2.2.1⟩, ⟨lt, ωκ₂.2.2.2⟩, Q₀⟩
    have hentry := congr_fun (congr_fun hAA_conj o₁) o₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry ⊢
    have hred :
        ∑ out : (Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1),
          star (Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l out o₁) *
            Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l out o₂ =
        ∑ μ : MSet Nminus l lt,
          star (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ ωκ₁) *
            Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt μ ωκ₂ := by
      rw [Fintype.sum_sigma]
      have hμ_step : ∀ μ : {μ : ΛG // l ∈ Nminus μ},
          ∑ x : AdBas BH Nminus μ.1,
            star (Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l ⟨μ, x⟩ o₁) *
              Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l ⟨μ, x⟩ o₂ =
          if hμ : lt ∈ Nminus μ.1 then
            star (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt ⟨μ.1, μ.2, hμ⟩ ωκ₁) *
              Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt ⟨μ.1, μ.2, hμ⟩ ωκ₂
          else 0 := by
        intro μ
        rw [Fintype.sum_sigma]
        by_cases hμ : lt ∈ Nminus μ.1
        · rw [dif_pos hμ, Finset.sum_eq_single ⟨lt, hμ⟩]
          · rw [Finset.sum_eq_single Q₀]
            · simp [Aop, o₁, o₂]
            · intro Q' _ hQ'
              simp [Aop, o₁, hQ']
            · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
          · intro lt' _ hlt'
            refine Finset.sum_eq_zero fun Q' _ => ?_
            have hne : lt'.1 ≠ lt := fun h => hlt' (Subtype.ext h)
            simp [Aop, o₁, hne]
          · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
        · rw [dif_neg hμ]
          refine Finset.sum_eq_zero fun lt' _ => Finset.sum_eq_zero fun Q' _ => ?_
          have hne : lt'.1 ≠ lt := fun h => hμ (h ▸ lt'.2)
          simp [Aop, o₁, hne]
      simp_rw [hμ_step]
      trans ∑ μ : {μ : {μ : ΛG // l ∈ Nminus μ} // lt ∈ Nminus μ.1},
          star (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt ⟨μ.1.1, μ.1.2, μ.2⟩ ωκ₁) *
            Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt ⟨μ.1.1, μ.1.2, μ.2⟩ ωκ₂
      · convert sum_dite_eq_sum_subtype (fun μ : {μ : ΛG // l ∈ Nminus μ} => lt ∈ Nminus μ.1)
          (fun μ =>
            star (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt ⟨μ.1.1, μ.1.2, μ.2⟩ ωκ₁) *
              Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt ⟨μ.1.1, μ.1.2, μ.2⟩ ωκ₂)
      · let eM : {μ : {μ : ΛG // l ∈ Nminus μ} // lt ∈ Nminus μ.1} ≃ MSet Nminus l lt :=
          { toFun := fun μ => ⟨μ.1.1, μ.1.2, μ.2⟩
            invFun := fun μ => ⟨⟨μ.1, μ.2.1⟩, μ.2.2⟩
            left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
            right_inv := fun ⟨_, _, _⟩ => rfl }
        exact Fintype.sum_equiv eM _ _ fun _ => rfl
    rw [← hred, hentry]
    have heq : o₁ = o₂ ↔ ωκ₁ = ωκ₂ := by
      constructor
      · intro h
        rcases ωκ₁ with ⟨ω₁, κ₁, h1a, h1b⟩
        rcases ωκ₂ with ⟨ω₂, κ₂, h2a, h2b⟩
        have hω : ω₁ = ω₂ := congrArg Sigma.fst h
        subst hω
        have hκ : κ₁ = κ₂ := by
          have hs := congrArg Sigma.fst (eq_of_heq (Sigma.ext_iff.mp h).2)
          exact congrArg Subtype.val hs
        subst hκ
        rfl
      · intro h
        subst h
        rfl
    exact if_congr heq rfl rfl
