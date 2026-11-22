-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:45:16.847911+00:00
-- url     : https://prove2.me/submissions/1115f8c9-eac5-4f86-9f0e-4a01e3e78fe5

import Definitions.Def_GL2QFT_Supplement_Beals
import Definitions.Def_GL2QFT_Supplement_RepTheory

noncomputable section

open Classical
open scoped Matrix ComplexConjugate
open GL2QFT GL2QFT.Induction GL2QFT.Supplement GL2QFT.Supplement.Beals

namespace GL2QFT.Supplement.BealsProof

/-! ### Part 1: Unitary representations, Schur's lemma, Schur orthogonality, Peter–Weyl completeness -/

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
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA g]

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
    rw [mul_sub, sub_mul, hA g, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
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
        = ∑ g : K, R₂ x * (R₂ g * M * R₁ g⁻¹) := by dsimp only [A]; rw [Matrix.mul_sum]
      _ = ∑ g : K, R₂ (x * g) * M * R₁ g⁻¹ := by
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [Matrix.mul_assoc, h2.1.2]
      _ = ∑ h : K, R₂ h * M * R₁ (x⁻¹ * h)⁻¹ := by
          refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun g => ?_
          dsimp [Equiv.mulLeft]
          simp
      _ = ∑ h : K, (R₂ h * M * R₁ h⁻¹) * R₁ x := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [mul_inv_rev, inv_inv, h1.1.2]
          simp only [Matrix.mul_assoc]
      _ = A * R₁ x := by dsimp only [A]; rw [Matrix.sum_mul]
  have hA0 : A = 0 := schur_zero_of_not_repEquiv hi1 hi2 hne hA
  have hAentry : A i i' = ∑ g : K, R₂ g i j * star (R₁ g i' j') := by
    simp only [A, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [isUnitaryRep_inv_eq_conjTranspose h1 g, Matrix.mul_apply]
    have hmul : ∀ k, (R₂ g * M) i k = if k = j' then R₂ g i j else 0 := by
      intro k
      simp only [M, Matrix.mul_apply, Matrix.single, Matrix.of_apply]
      rw [Finset.sum_eq_single j]
      · by_cases hjk : j' = k
        · subst hjk; simp
        · simp [hjk, Ne.symm hjk]
      · intro a _ ha
        simp [ha.symm]
      · intro hj
        exact False.elim (hj (Finset.mem_univ _))
    simp only [hmul, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Matrix.conjTranspose_apply]
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
        = ∑ g : K, R x * (R g * M * R g⁻¹) := by dsimp only [A]; rw [Matrix.mul_sum]
      _ = ∑ g : K, R (x * g) * M * R g⁻¹ := by
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [Matrix.mul_assoc, hR.1.2]
      _ = ∑ h : K, R h * M * R (x⁻¹ * h)⁻¹ := by
          refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun g => ?_
          dsimp [Equiv.mulLeft]
          simp
      _ = ∑ h : K, (R h * M * R h⁻¹) * R x := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [mul_inv_rev, inv_inv, hR.1.2]
          simp only [Matrix.mul_assoc]
      _ = A * R x := by dsimp only [A]; rw [Matrix.sum_mul]
  obtain ⟨c, hc⟩ := schur_eq_smul_one hi hA
  have htr1 : A.trace = c * (Fintype.card ι : ℂ) := by
    rw [hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_comm]
  have htr2 : A.trace = (Fintype.card K : ℂ) * (if j = j' then 1 else 0) := by
    simp only [A, Matrix.trace_sum]
    have hterm : ∀ g : K, (R g * M * R g⁻¹).trace = if j = j' then 1 else 0 := by
      intro g
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← hR.1.2, inv_mul_cancel, hR.1.1,
        Matrix.one_mul]
      simp only [M, Matrix.trace, Matrix.diag, Matrix.single, Matrix.of_apply]
      split_ifs with hjj
      · subst hjj
        rw [Finset.sum_eq_single j]
        · simp
        · intro a _ ha; simp [ha.symm]
        · intro hj; exact False.elim (hj (Finset.mem_univ _))
      · refine Finset.sum_eq_zero fun a _ => ?_
        by_cases haj : j = a
        · subst haj; simp [Ne.symm hjj]
        · simp [haj]
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
      simp only [M, Matrix.mul_apply, Matrix.single, Matrix.of_apply]
      rw [Finset.sum_eq_single j]
      · by_cases hjk : j' = k
        · subst hjk; simp
        · simp [hjk, Ne.symm hjk]
      · intro a _ ha
        simp [ha.symm]
      · intro hj
        exact False.elim (hj (Finset.mem_univ _))
    simp only [hmul, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Matrix.conjTranspose_apply]
  rw [← hAentry, hc, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hc_val]
  split_ifs <;> ring

private theorem fourierMatrix_mul_conjTranspose {K Λ : Type} [Group K] [Fintype K]
    [Fintype Λ] {B : Λ → Type} [∀ μ, Fintype (B μ)] [∀ μ, DecidableEq (B μ)]
    {R : ∀ μ, K → Matrix (B μ) (B μ) ℂ} (hR : IsIrrepSystem R) :
    fourierMatrix R * (fourierMatrix R)ᴴ = 1 := by
  ext ⟨μ, i, j⟩ ⟨μ', i', j'⟩
  simp only [Matrix.mul_apply, fourierMatrix, Matrix.of_apply, Matrix.conjTranspose_apply,
    star_mul', Complex.star_def, Complex.conj_ofReal, Matrix.one_apply]
  have hpull :
      ∑ g : K,
        ((Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ) * R μ g i j) *
          ((Real.sqrt ((Fintype.card (B μ') : ℝ) / (Fintype.card K : ℝ)) : ℂ) *
            conj (R μ' g i' j')) =
      (Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ) *
        (Real.sqrt ((Fintype.card (B μ') : ℝ) / (Fintype.card K : ℝ)) : ℂ) *
        ∑ g : K, R μ g i j * star (R μ' g i' j') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Complex.star_def]
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
      simp only [↓reduceIte, mul_one]
      field_simp
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
      simpa [ip, Complex.star_def, Complex.mul_re] using hre
    have hterm : (u g).re * (u g).re + (u g).im * (u g).im = 0 := by
      have hnn : ∀ x ∈ (Finset.univ : Finset K),
          0 ≤ (u x).re * (u x).re + (u x).im * (u x).im := fun x _ =>
        add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
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
      map_add' := fun f₁ f₂ => rfl
      map_smul' := fun c f => rfl }
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
      dsimp only [n]
      rw [← hUdim]
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
          have h1 := Matrix.toLin_apply b b (ρ x) (b.equivFun.symm v)
          rw [Matrix.toLin_toMatrix] at h1
          have h2 : ⇑(b.repr (b.equivFun.symm v)) = v := by
            ext i; exact congr_fun (b.equivFun.apply_symm_apply v) i
          rw [h1, h2, b.equivFun_symm_apply]
        refine ⟨L_U x (b.equivFun.symm v), ⟨(ρ x).mulVec v, hV x v hv, hLU.symm⟩, rfl⟩
      by_cases hbot : U'' = ⊥
      · left
        have hU'_bot : U' = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro x hx
          have : (x : K → ℂ) ∈ U'' := ⟨x, hx, rfl⟩
          rw [hbot] at this
          exact Subtype.ext this
        rw [Submodule.eq_bot_iff]
        intro v hv
        have : b.equivFun.symm v ∈ U' := ⟨v, hv, rfl⟩
        rw [hU'_bot] at this
        have hv0 := congrArg b.equivFun this
        rw [b.equivFun.apply_symm_apply, map_zero] at hv0
        exact hv0
      · right
        have hle_n : n ≤ Module.finrank ℂ U'' := Nat.find_min' hex
          ⟨U'', hU''_le.trans hUW, hbot, hU''_L, rfl⟩
        have hge_n : Module.finrank ℂ U'' ≤ n := by
          dsimp only [n]
          rw [← hUdim]
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
        have hv' : b.equivFun (b.equivFun.symm w) = b.equivFun (b.equivFun.symm v) :=
          congrArg b.equivFun hvw
        rw [b.equivFun.apply_symm_apply, b.equivFun.apply_symm_apply] at hv'
        subst hv'
        exact hw
    obtain ⟨μ, P_mat, Q_mat, hPQ, hQP, hPQ_inter⟩ := hR.2.2.2 (Fin n) ρ hρ_mat hρ_irred
    have hρ_conj : ∀ x : K, ρ x = P_mat * R μ x * Q_mat := by
      intro x
      calc ρ x = ρ x * (P_mat * Q_mat) := by rw [hPQ, Matrix.mul_one]
        _ = (ρ x * P_mat) * Q_mat := (Matrix.mul_assoc _ _ _).symm
        _ = (P_mat * R μ x) * Q_mat := by rw [hPQ_inter x (Set.mem_univ _)]
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
      (∑ c : Fin n, P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1) *
        (Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ)⁻¹
    have hu_in_W_eq : u = ∑ i : B μ, ∑ j : B μ, coeff i j • φ ⟨μ, j, i⟩ := by
      ext g
      rw [hu_eq g]
      simp only [hρ_conj g⁻¹, isUnitaryRep_inv_eq_conjTranspose (hR.1 μ) g, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, φ,
        fourierMatrix, Matrix.of_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
      have hswap :
          ∑ c : Fin n, (∑ j : B μ, (∑ i : B μ, P_mat c i * conj (R μ g j i)) * Q_mat j a₀) *
            (b c : K → ℂ) 1 =
          ∑ i : B μ, ∑ j : B μ, (∑ c : Fin n, P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1) *
            conj (R μ g j i) := by
        calc ∑ c : Fin n, (∑ j : B μ, (∑ i : B μ, P_mat c i * conj (R μ g j i)) * Q_mat j a₀) *
              (b c : K → ℂ) 1
            = ∑ c : Fin n, ∑ j : B μ, ∑ i : B μ,
                P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1 * conj (R μ g j i) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              simp only [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
          _ = ∑ j : B μ, ∑ c : Fin n, ∑ i : B μ,
                P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1 * conj (R μ g j i) := Finset.sum_comm
          _ = ∑ j : B μ, ∑ i : B μ, ∑ c : Fin n,
                P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1 * conj (R μ g j i) :=
              Finset.sum_congr rfl fun j _ => Finset.sum_comm
          _ = ∑ i : B μ, ∑ j : B μ, ∑ c : Fin n,
                P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1 * conj (R μ g j i) := Finset.sum_comm
          _ = ∑ i : B μ, ∑ j : B μ, (∑ c : Fin n, P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1) *
                conj (R μ g j i) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
                (Finset.sum_mul _ _ _).symm
      rw [hswap]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [coeff]
      rw [mul_assoc, ← mul_assoc (Real.sqrt ((Fintype.card (B μ) : ℝ) / (Fintype.card K : ℝ)) : ℂ)⁻¹,
        inv_mul_cancel₀ hsqrt_ne, one_mul]
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
          calc ip (φ b) w
              = ∑ g : K, star (φ b g) * ∑ a, ip (φ a) u * φ a g := by
                simp [ip, w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            _ = ∑ g : K, ∑ a, star (φ b g) * (ip (φ a) u * φ a g) := by
                refine Finset.sum_congr rfl fun g _ => Finset.mul_sum _ _ _
            _ = ∑ a, ∑ g : K, star (φ b g) * (ip (φ a) u * φ a g) := Finset.sum_comm
            _ = ∑ a, ip (φ a) u * ip (φ b) (φ a) := by
                refine Finset.sum_congr rfl fun a _ => ?_
                simp only [ip, Finset.mul_sum]
                refine Finset.sum_congr rfl fun g _ => by ring
            _ = ∑ a, ip (φ a) u * (if b = a then 1 else 0) := by
                refine Finset.sum_congr rfl fun a _ => by rw [hip_φ b a]
            _ = ip (φ b) u := by
                simp [Finset.mem_univ]
        rw [h1, h2, sub_self]
      · simp [ip]
      · intro v₁ v₂ _ _ h₁ h₂
        have : ip (v₁ + v₂) (u - w) = ip v₁ (u - w) + ip v₂ (u - w) := by
          simp [ip, add_mul, Finset.sum_add_distrib]
        rw [this, h₁, h₂, add_zero]
      · intro c v _ hv
        have : ip (c • v) (u - w) = star c * ip v (u - w) := by
          simp [ip, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring
        rw [this, hv, mul_zero]
    rw [hWperp_bot] at hdiff
    exact sub_eq_zero.mp hdiff
  ext g g'
  have hsing := congr_fun (hproj (Pi.single g' (1 : ℂ) : K → ℂ)) g
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have hip_sing : ∀ a, ip (φ a) (Pi.single g' (1 : ℂ) : K → ℂ) = fourierMatrix R a g' := by
    intro a
    simp only [ip, φ, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, star_star]
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hip_sing] at hsing
  have hsing_g : (Pi.single g' (1 : ℂ) : K → ℂ) g = if g = g' then 1 else 0 := by
    simp [Pi.single_apply]
  rw [hsing_g] at hsing
  convert hsing.symm using 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [φ, mul_comm]

/-! ### Part 2: Lemma 3.5, unitarity of `UIndLam`, Lemma 3.4, and Lemma 4.2 -/

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
  let th₀ := e.symm g
  let t := th₀.1
  let h := th₀.2
  have hth_eq : g = (t : G) * (h : G) := (e.apply_symm_apply g).symm
  dsimp only [Matrix.submatrix_apply, id_eq]
  rw [Matrix.mul_apply]
  have hsum_th :
      ∑ th : T × H,
        (UIndTensorI T BH Nminus RG * Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH))
          (ident BH Nminus ⟨μ, Q, ⟨⟨l, hl⟩, R⟩⟩) th *
          Enc H T th g =
      (UIndTensorI T BH Nminus RG * Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH))
        (ident BH Nminus ⟨μ, Q, ⟨⟨l, hl⟩, R⟩⟩) (t, h) := by
    rw [Finset.sum_eq_single (t, h)]
    · simp only [Enc, Matrix.of_apply, if_pos hth_eq, mul_one]
    · intro th _ hth
      have hne : g ≠ (th.1 : G) * (th.2 : G) := fun heq =>
        hth (e.injective (hth_eq.symm.trans heq).symm)
      simp only [Enc, Matrix.of_apply, if_neg hne, mul_zero]
    · intro hth; exact False.elim (hth (Finset.mem_univ _))
  rw [hsum_th, Matrix.mul_apply]
  simp only [UIndTensorI, Matrix.of_apply, ident, UIndLam]
  have hkr : ∀ x : T × Σ l' : ΛH, BH l' × BH l',
      Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH) x (t, h) =
        (if x.1 = t then (1 : ℂ) else 0) *
          ((Real.sqrt ((Fintype.card (BH x.2.1) : ℝ) / (Fintype.card H : ℝ)) : ℂ) *
            RH x.2.1 h x.2.2.1 x.2.2.2) := by
    intro ⟨a, ⟨l', P', R'⟩⟩
    simp [Matrix.one_apply, fourierMatrix]
  simp_rw [hkr]
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
  simp only [fourierMatrix, Matrix.of_apply]
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
      dsimp only at this
      rw [dif_pos rfl] at this
      dsimp only [cast_eq] at this
      rw [this]
    · intro l' _ hl'
      refine Finset.sum_eq_zero fun P' _ => ?_
      have := hAd μ h ⟨l', P'⟩ ⟨⟨l, hl⟩, R⟩
      dsimp only at this
      rw [dif_neg hl'] at this
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

private theorem uindTensorI_conjTranspose_mul {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG) :
    (UIndTensorI T BH Nminus RG)ᴴ * UIndTensorI T BH Nminus RG = 1 := by
  let eId := identEquiv BH Nminus
  let FG' : Matrix (RHSOut BH Nminus) G ℂ := (fourierMatrix RG).submatrix eId.symm id
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
    rw [kronecker_conjTranspose, Matrix.conjTranspose_one]
    rw [show Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH) *
          Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH)ᴴ =
        Matrix.kronecker ((1 : Matrix T T ℂ) * 1) (fourierMatrix RH * (fourierMatrix RH)ᴴ) from
      (Matrix.mul_kronecker_mul _ _ _ _).symm]
    rw [Matrix.mul_one, fourierMatrix_mul_conjTranspose hRH]
    ext ⟨t₁, x₁⟩ ⟨t₂, x₂⟩
    by_cases ht : t₁ = t₂ <;> by_cases hx : x₁ = x₂ <;> simp [Matrix.one_apply, ht, hx]
  have hK_mul' : Kᴴ * K = 1 := by
    dsimp only [K]
    rw [kronecker_conjTranspose, Matrix.conjTranspose_one]
    rw [show Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH)ᴴ *
          Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH) =
        Matrix.kronecker ((1 : Matrix T T ℂ) * 1) ((fourierMatrix RH)ᴴ * fourierMatrix RH) from
      (Matrix.mul_kronecker_mul _ _ _ _).symm]
    rw [Matrix.mul_one, fourierMatrix_conjTranspose_mul hRH]
    ext ⟨t₁, x₁⟩ ⟨t₂, x₂⟩
    by_cases ht : t₁ = t₂ <;> by_cases hx : x₁ = x₂ <;> simp [Matrix.one_apply, ht, hx]
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
    have h1 := congr_fun (congr_fun hfact (eId.symm r)) g
    simp only [Matrix.submatrix_apply, id_eq] at h1
    dsimp only [FG', M, K]
    rw [← Matrix.mul_assoc]
    exact h1
  have hU_eq : UIndTensorI T BH Nminus RG = FG' * Mᴴ := by
    calc UIndTensorI T BH Nminus RG
        = UIndTensorI T BH Nminus RG * (M * Mᴴ) := by rw [hM_mul, Matrix.mul_one]
      _ = (UIndTensorI T BH Nminus RG * M) * Mᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = FG' * Mᴴ := by rw [← hFG'_eq]
  calc (UIndTensorI T BH Nminus RG)ᴴ * UIndTensorI T BH Nminus RG
      = (M * FG'ᴴ) * (FG' * Mᴴ) := by
          rw [hU_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    _ = M * (FG'ᴴ * FG') * Mᴴ := by simp only [Matrix.mul_assoc]
    _ = M * Mᴴ := by rw [hFG'_unit, Matrix.mul_one]
    _ = 1 := hM_mul

private theorem uindLam_conjTranspose_mul {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG) (l : ΛH) :
    (UIndLam T BH Nminus RG l)ᴴ * UIndLam T BH Nminus RG l = 1 := by
  have : Nonempty (BH l) := (hRH.2.1 l).1
  obtain ⟨R₀⟩ := this
  have hU := uindTensorI_conjTranspose_mul H T hT BH Nminus RH hRH RG hRG hAd
  ext ⟨t₁, P₁⟩ ⟨t₂, P₂⟩
  have hentry := congr_fun (congr_fun hU (t₁, ⟨l, P₁, R₀⟩)) (t₂, ⟨l, P₂, R₀⟩)
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

private def blockDiagRG {G ΛH ΛG : Type} (BH : ΛH → Type) (Nminus : ΛG → Finset ΛH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (l : ΛH) (g : G) :
    Matrix (Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1)
           (Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1) ℂ :=
  Matrix.of fun M N =>
    if e : M.1 = N.1 then
      RG M.1.1 g M.2 (cast (congrArg (fun μ : {μ : ΛG // l ∈ Nminus μ} => AdBas BH Nminus μ.1) e.symm) N.2)
    else 0

private theorem uindLam_intertwines {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (hRG : ∀ μ, IsMatRep (RG μ)) (hAd : IsSubgroupAdapted H BH Nminus RH RG)
    (l : ΛH) (g : G) :
    UIndLam T BH Nminus RG l * indRep H T (RH l) g =
      blockDiagRG BH Nminus RG l g * UIndLam T BH Nminus RG l := by
  let e : T × H ≃ G := Equiv.ofBijective _ hT
  ext ⟨⟨μ, hμ⟩, Q⟩ ⟨t, P⟩
  let tghg := e.symm (g * (t : G))
  let tg := tghg.1
  let hg := tghg.2
  have hgt : g * (t : G) = (tg : G) * (hg : G) := (e.apply_symm_apply (g * (t : G))).symm
  simp only [Matrix.mul_apply, UIndLam, indRep, blockDiagRG, Matrix.of_apply]
  have hLHS :
      ∑ sR : T × BH l,
        ((Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
          ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
          RG μ (sR.1 : G) Q ⟨⟨l, hμ⟩, sR.2⟩) *
        (if h : ((sR.1 : G)⁻¹ * g * (t : G)) ∈ H then RH l ⟨_, h⟩ sR.2 P else 0) =
      (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
        ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
        ∑ R : BH l, RG μ (tg : G) Q ⟨⟨l, hμ⟩, R⟩ * RH l hg R P := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single tg]
    · have hmem : ((tg : G)⁻¹ * g * (t : G)) ∈ H := by
        rw [mul_assoc, hgt, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hg.2
      have heq_hg : (⟨(tg : G)⁻¹ * g * (t : G), hmem⟩ : H) = hg := by
        apply Subtype.ext
        dsimp only
        rw [mul_assoc, hgt, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun R _ => ?_
      rw [dif_pos hmem, heq_hg, mul_assoc]
    · intro s _ hs
      refine Finset.sum_eq_zero fun R _ => ?_
      have hnot : ((s : G)⁻¹ * g * (t : G)) ∉ H := by
        intro hm
        have heq_mul : e (s, ⟨(s : G)⁻¹ * g * (t : G), hm⟩) = e (tg, hg) := by
          change (s : G) * ((s : G)⁻¹ * g * (t : G)) = (tg : G) * (hg : G)
          rw [← mul_assoc (s : G), ← mul_assoc (s : G), mul_inv_cancel, one_mul, hgt]
        exact hs (congrArg Prod.fst (e.injective heq_mul))
      rw [dif_neg hnot, mul_zero]
    · intro htg; exact False.elim (htg (Finset.mem_univ _))
  have hRHS :
      ∑ M : Σ μ' : {μ' : ΛG // l ∈ Nminus μ'}, AdBas BH Nminus μ'.1,
        (if e' : (⟨μ, hμ⟩ : {μ' : ΛG // l ∈ Nminus μ'}) = M.1 then
          RG μ g Q (cast (congrArg (fun μ' : {μ' : ΛG // l ∈ Nminus μ'} => AdBas BH Nminus μ'.1) e'.symm) M.2)
        else 0) *
        ((Real.sqrt ((Fintype.card (AdBas BH Nminus M.1.1) : ℝ) /
          ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
          RG M.1.1 (t : G) M.2 ⟨⟨l, M.1.2⟩, P⟩) =
      (Real.sqrt ((Fintype.card (AdBas BH Nminus μ) : ℝ) /
        ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
        ∑ S : AdBas BH Nminus μ, RG μ g Q S * RG μ (t : G) S ⟨⟨l, hμ⟩, P⟩ := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single ⟨μ, hμ⟩]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      dsimp only
      rw [dif_pos rfl]
      dsimp only [cast_eq]
      ring
    · intro μ' _ hμ'
      refine Finset.sum_eq_zero fun S _ => ?_
      simp [Ne.symm hμ']
    · intro hμ''; exact False.elim (hμ'' (Finset.mem_univ _))
  rw [hLHS, hRHS]
  congr 1
  have had_sum :
      ∑ R : BH l, RG μ (tg : G) Q ⟨⟨l, hμ⟩, R⟩ * RH l hg R P =
        ∑ S : AdBas BH Nminus μ, RG μ (tg : G) Q S * RG μ (hg : G) S ⟨⟨l, hμ⟩, P⟩ := by
    symm
    rw [Fintype.sum_sigma, Finset.sum_eq_single ⟨l, hμ⟩]
    · refine Finset.sum_congr rfl fun R _ => ?_
      have := hAd μ hg ⟨⟨l, hμ⟩, R⟩ ⟨⟨l, hμ⟩, P⟩
      dsimp only at this
      rw [dif_pos rfl] at this
      dsimp only [cast_eq] at this
      rw [this]
    · intro l' _ hl'
      refine Finset.sum_eq_zero fun R _ => ?_
      have := hAd μ hg ⟨l', R⟩ ⟨⟨l, hμ⟩, P⟩
      dsimp only at this
      rw [dif_neg hl'] at this
      rw [this, mul_zero]
    · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
  rw [had_sum, ← Matrix.mul_apply, ← (hRG μ).2 (tg : G) (hg : G), ← hgt,
    ← Matrix.mul_apply, ← (hRG μ).2 g (t : G)]

private theorem lemma_4_2_not_mem {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G)) (he : (1 : G) ∈ T)
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG)
    {g : G} (hg : g ∉ H) (l : ΛH) (Q P : BH l) :
    ∑ μ : ΛG, (if h : l ∈ Nminus μ then
      ((dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) *
        RG μ g ⟨⟨l, h⟩, Q⟩ ⟨⟨l, h⟩, P⟩
    else 0) = 0 := by
  have hint := uindLam_intertwines H T hT BH Nminus RH RG (fun μ => (hRG.1 μ).1) hAd l g
  have hunit := uindLam_conjTranspose_mul H T hT BH Nminus RH hRH RG hRG hAd l
  have hind : indRep H T (RH l) g =
      (UIndLam T BH Nminus RG l)ᴴ * blockDiagRG BH Nminus RG l g * UIndLam T BH Nminus RG l := by
    calc indRep H T (RH l) g
        = 1 * indRep H T (RH l) g := (Matrix.one_mul _).symm
      _ = ((UIndLam T BH Nminus RG l)ᴴ * UIndLam T BH Nminus RG l) * indRep H T (RH l) g := by
          rw [hunit]
      _ = (UIndLam T BH Nminus RG l)ᴴ * (UIndLam T BH Nminus RG l * indRep H T (RH l) g) :=
          Matrix.mul_assoc _ _ _
      _ = (UIndLam T BH Nminus RG l)ᴴ * (blockDiagRG BH Nminus RG l g * UIndLam T BH Nminus RG l) := by
          rw [hint]
      _ = (UIndLam T BH Nminus RG l)ᴴ * blockDiagRG BH Nminus RG l g * UIndLam T BH Nminus RG l :=
          (Matrix.mul_assoc _ _ _).symm
  let t1 : T := ⟨1, he⟩
  have heval := congr_fun (congr_fun hind (t1, Q)) (t1, P)
  have hLHS : indRep H T (RH l) g (t1, Q) (t1, P) = 0 := by
    simp only [indRep, Matrix.of_apply, t1, inv_one, one_mul, mul_one]
    exact dif_neg hg
  rw [hLHS] at heval
  have hRHS :
      ((UIndLam T BH Nminus RG l)ᴴ * blockDiagRG BH Nminus RG l g * UIndLam T BH Nminus RG l)
        (t1, Q) (t1, P) =
      ∑ μ : ΛG, (if h : l ∈ Nminus μ then
        ((dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) *
          RG μ g ⟨⟨l, h⟩, Q⟩ ⟨⟨l, h⟩, P⟩
      else 0) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, UIndLam, blockDiagRG, Matrix.of_apply,
      t1]
    have hU_one : ∀ (μ : {μ : ΛG // l ∈ Nminus μ}) (B : AdBas BH Nminus μ.1) (R : BH l),
        RG μ.1 (1 : G) B ⟨⟨l, μ.2⟩, R⟩ = if B = ⟨⟨l, μ.2⟩, R⟩ then 1 else 0 := by
      intro μ B R
      rw [(hRG.1 μ.1).1.1, Matrix.one_apply]
    have hsum1 :
        ∑ M : Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1,
          (∑ N : Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1,
            star ((Real.sqrt ((Fintype.card (AdBas BH Nminus N.1.1) : ℝ) /
              ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
              RG N.1.1 (1 : G) N.2 ⟨⟨l, N.1.2⟩, Q⟩) *
            (if e : N.1 = M.1 then
              RG N.1.1 g N.2 (cast (congrArg (fun μ : {μ : ΛG // l ∈ Nminus μ} => AdBas BH Nminus μ.1) e.symm) M.2)
            else 0)) *
          ((Real.sqrt ((Fintype.card (AdBas BH Nminus M.1.1) : ℝ) /
            ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
            RG M.1.1 (1 : G) M.2 ⟨⟨l, M.1.2⟩, P⟩) =
        ∑ μ : {μ : ΛG // l ∈ Nminus μ},
          ((dG BH Nminus μ.1 / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) *
            RG μ.1 g ⟨⟨l, μ.2⟩, Q⟩ ⟨⟨l, μ.2⟩, P⟩ := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.sum_eq_single ⟨⟨l, μ.2⟩, P⟩]
      · rw [Fintype.sum_sigma, Finset.sum_eq_single μ]
        · rw [Finset.sum_eq_single ⟨⟨l, μ.2⟩, Q⟩]
          · dsimp only
            rw [dif_pos rfl]
            dsimp only [cast_eq]
            rw [hU_one μ ⟨⟨l, μ.2⟩, Q⟩ Q, if_pos rfl, mul_one,
              hU_one μ ⟨⟨l, μ.2⟩, P⟩ P, if_pos rfl, mul_one]
            rw [Complex.star_def, Complex.conj_ofReal]
            have hsq :
                (Real.sqrt ((Fintype.card (AdBas BH Nminus μ.1) : ℝ) /
                  ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
                (Real.sqrt ((Fintype.card (AdBas BH Nminus μ.1) : ℝ) /
                  ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) =
                ((dG BH Nminus μ.1 / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) := by
              rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
              congr 1
              simp [dG, dH, mul_comm]
            rw [mul_right_comm _ (RG μ.1 g _ _), hsq]
          · intro B _ hB
            simp [hU_one μ B Q, hB]
          · intro hQ'; exact False.elim (hQ' (Finset.mem_univ _))
        · intro μ' _ hμ'
          refine Finset.sum_eq_zero fun B _ => ?_
          simp [hμ']
        · intro hμ'; exact False.elim (hμ' (Finset.mem_univ _))
      · intro B _ hB
        simp [hU_one μ B P, hB]
      · intro hP'; exact False.elim (hP' (Finset.mem_univ _))
    rw [hsum1]
    have hsub :
        ∑ μ : {μ : ΛG // l ∈ Nminus μ},
          ((dG BH Nminus μ.1 / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) *
            RG μ.1 g ⟨⟨l, μ.2⟩, Q⟩ ⟨⟨l, μ.2⟩, P⟩ =
        ∑ μ : ΛG, (if h : l ∈ Nminus μ then
          ((dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) *
            RG μ g ⟨⟨l, h⟩, Q⟩ ⟨⟨l, h⟩, P⟩
        else 0) := by
      let f : ΛG → ℂ := fun μ =>
        if h : l ∈ Nminus μ then
          ((dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) *
            RG μ g ⟨⟨l, h⟩, Q⟩ ⟨⟨l, h⟩, P⟩
        else 0
      have hpart : ∑ μ : ΛG, f μ =
          ∑ μ ∈ Finset.univ.filter (fun μ : ΛG => l ∈ Nminus μ), f μ +
            ∑ μ ∈ Finset.univ.filter (fun μ : ΛG => l ∉ Nminus μ), f μ :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ (fun μ : ΛG => l ∈ Nminus μ) f).symm
      have hzero : ∑ μ ∈ Finset.univ.filter (fun μ : ΛG => l ∉ Nminus μ), f μ = 0 := by
        refine Finset.sum_eq_zero fun μ hμ => ?_
        exact dif_neg (Finset.mem_filter.mp hμ).2
      have hbij :
          ∑ μ : {μ : ΛG // l ∈ Nminus μ},
            ((dG BH Nminus μ.1 / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) *
              RG μ.1 g ⟨⟨l, μ.2⟩, Q⟩ ⟨⟨l, μ.2⟩, P⟩ =
          ∑ μ ∈ Finset.univ.filter (fun μ : ΛG => l ∈ Nminus μ), f μ := by
        refine Finset.sum_bij (fun (μ : {μ : ΛG // l ∈ Nminus μ}) _ => μ.1)
          (fun μ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, μ.2⟩)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun μ hμ => ⟨⟨μ, (Finset.mem_filter.mp hμ).2⟩, Finset.mem_univ _, rfl⟩)
          (fun μ _ => by dsimp [f]; rw [dif_pos μ.2])
      change _ = ∑ μ : ΛG, f μ
      rw [hpart, hzero, add_zero, hbij]
    exact hsub
  exact (hRHS.symm.trans heval.symm)

/-! ### Part 3: Gate actions and Beals circuit evaluation -/

private def regVec {G : Type} (T : Set G) {ΛH ΛG : Type} {BH : ΛH → Type}
    {Nminus : ΛG → Finset ΛH} {Mod : Type} (emb : ∀ l, BH l → Mod)
    (μ : ΛG) (Q : AdBas BH Nminus μ) (c : ΛH) : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) :=
  (none, (encAd BH Nminus Mod emb μ Q).1, (encAd BH Nminus Mod emb μ Q).2, some μ, c)

private theorem regVec_inj {G : Type} {T : Set G} {ΛH ΛG : Type} {BH : ΛH → Type}
    {Nminus : ΛG → Finset ΛH} {Mod : Type} (emb : ∀ l, BH l → Mod)
    (hemb : ∀ l, Function.Injective (emb l))
    {μ₁ μ₂ : ΛG} {Q₁ : AdBas BH Nminus μ₁} {Q₂ : AdBas BH Nminus μ₂} {c₁ c₂ : ΛH}
    (h : regVec T emb μ₁ Q₁ c₁ = regVec T emb μ₂ Q₂ c₂) :
    μ₁ = μ₂ ∧ c₁ = c₂ ∧ HEq Q₁ Q₂ := by
  have h1 : μ₁ = μ₂ := Option.some.inj (congrArg (fun r : Reg T Mod => r.2.2.2.1) h)
  have h2 : c₁ = c₂ := congrArg (fun r : Reg T Mod => r.2.2.2.2) h
  subst h1; subst h2
  refine ⟨rfl, rfl, heq_of_eq ?_⟩
  have hl : Q₁.1.1 = Q₂.1.1 := Option.some.inj (congrArg (fun r : Reg T Mod => r.2.2.1) h)
  rcases Q₁ with ⟨⟨l₁, hl₁⟩, P₁⟩
  rcases Q₂ with ⟨⟨l₂, hl₂⟩, P₂⟩
  dsimp at hl
  subst hl
  have hP : emb l₁ P₁ = emb l₁ P₂ := congrArg (fun r : Reg T Mod => r.2.1) h
  have := hemb l₁ hP
  subst this
  rfl

private theorem rgate_mulVec_ket_vec {G : Type} [Fintype G] {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {BH : ΛH → Type} [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] {Nminus : ΛG → Finset ΛH} {Mod : Type} [Fintype Mod]
    (emb : ∀ l, BH l → Mod) (hemb : ∀ l, Function.Injective (emb l))
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (τ : T)
    (μ : ΛG) (Q : AdBas BH Nminus μ) (c : ΛH) :
    (Rgate T BH Nminus Mod emb RG τ).mulVec (ket T Mod (regVec T emb μ Q c)) =
      ∑ Q' : AdBas BH Nminus μ,
        (RG μ (τ : G) Q' Q) • ket T Mod (regVec T emb μ Q' c) := by
  ext r'
  simp only [Matrix.mulVec, dotProduct, Rgate, ket, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.sum_apply, Matrix.single, Matrix.of_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (regVec T emb μ Q c)]
  · simp only [↓reduceIte, mul_one]
    have h1 :
        ∑ c' : ΛH, ∑ μ' : ΛG, ∑ Q' : AdBas BH Nminus μ',
          (if regVec T emb μ' Q' c' = r' ∧ regVec T emb μ' Q' c' = regVec T emb μ Q c then (1 : ℂ) else 0) =
        if r' = regVec T emb μ Q c then 1 else 0 := by
      rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single μ]
        · rw [Finset.sum_eq_single Q]
          · simp [eq_comm]
          · intro Q' _ hQ'
            have hne : regVec T emb μ Q' c ≠ regVec T emb μ Q c := fun h => by
              obtain ⟨_, _, hheq⟩ := regVec_inj emb hemb h
              exact hQ' (eq_of_heq hheq)
            simp [hne]
          · intro hQ; exact False.elim (hQ (Finset.mem_univ _))
        · intro μ' _ hμ'
          refine Finset.sum_eq_zero fun Q' _ => ?_
          have hne : regVec T emb μ' Q' c ≠ regVec T emb μ Q c := fun h =>
            hμ' (regVec_inj emb hemb h).1
          simp [hne]
        · intro hμ; exact False.elim (hμ (Finset.mem_univ _))
      · intro c' _ hc'
        refine Finset.sum_eq_zero fun μ' _ => Finset.sum_eq_zero fun Q' _ => ?_
        have hne : regVec T emb μ' Q' c' ≠ regVec T emb μ Q c := fun h =>
          hc' (regVec_inj emb hemb h).2.1
        simp [hne]
      · intro hc; exact False.elim (hc (Finset.mem_univ _))
    have h2 :
        ∑ c' : ΛH, ∑ μ' : ΛG, ∑ Q' : AdBas BH Nminus μ', ∑ Q'' : AdBas BH Nminus μ',
          (if regVec T emb μ' Q' c' = r' ∧ regVec T emb μ' Q'' c' = regVec T emb μ Q c then
            RG μ' (τ : G) Q' Q'' else 0) =
        ∑ Q' : AdBas BH Nminus μ, RG μ (τ : G) Q' Q * (if r' = regVec T emb μ Q' c then 1 else 0) := by
      rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single μ]
        · refine Finset.sum_congr rfl fun Q' _ => ?_
          rw [Finset.sum_eq_single Q]
          · simp [eq_comm]
          · intro Q'' _ hQ''
            have hne : regVec T emb μ Q'' c ≠ regVec T emb μ Q c := fun h => by
              obtain ⟨_, _, hheq⟩ := regVec_inj emb hemb h
              exact hQ'' (eq_of_heq hheq)
            simp [hne]
          · intro hQ; exact False.elim (hQ (Finset.mem_univ _))
        · intro μ' _ hμ'
          refine Finset.sum_eq_zero fun Q' _ => Finset.sum_eq_zero fun Q'' _ => ?_
          have hne : regVec T emb μ' Q'' c ≠ regVec T emb μ Q c := fun h =>
            hμ' (regVec_inj emb hemb h).1
          simp [hne]
        · intro hμ; exact False.elim (hμ (Finset.mem_univ _))
      · intro c' _ hc'
        refine Finset.sum_eq_zero fun μ' _ =>
          Finset.sum_eq_zero fun Q' _ => Finset.sum_eq_zero fun Q'' _ => ?_
        have hne : regVec T emb μ' Q'' c' ≠ regVec T emb μ Q c := fun h =>
          hc' (regVec_inj emb hemb h).2.1
        simp [hne]
      · intro hc; exact False.elim (hc (Finset.mem_univ _))
    change (if r' = regVec T emb μ Q c then (1 : ℂ) else 0) -
        ∑ c' : ΛH, ∑ μ' : ΛG, ∑ Q' : AdBas BH Nminus μ',
          (if regVec T emb μ' Q' c' = r' ∧ regVec T emb μ' Q' c' = regVec T emb μ Q c then (1 : ℂ) else 0) +
        ∑ c' : ΛH, ∑ μ' : ΛG, ∑ Q' : AdBas BH Nminus μ', ∑ Q'' : AdBas BH Nminus μ',
          (if regVec T emb μ' Q' c' = r' ∧ regVec T emb μ' Q'' c' = regVec T emb μ Q c then
            RG μ' (τ : G) Q' Q'' else 0) =
      ∑ Q' : AdBas BH Nminus μ, RG μ (τ : G) Q' Q * (if r' = regVec T emb μ Q' c then 1 else 0)
    rw [h1, h2]
    ring
  · intro r _ hr; simp [hr]
  · intro hr; exact False.elim (hr (Finset.mem_univ _))

private theorem rgate_mulVec_ket_not_vec {G : Type} [Fintype G] {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {BH : ΛH → Type} [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] {Nminus : ΛG → Finset ΛH} {Mod : Type} [Fintype Mod]
    (emb : ∀ l, BH l → Mod)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (τ : T)
    (r : Reg T Mod (ΛH := ΛH) (ΛG := ΛG))
    (hr : ∀ (μ : ΛG) (Q : AdBas BH Nminus μ) (c : ΛH), r ≠ regVec T emb μ Q c) :
    (Rgate T BH Nminus Mod emb RG τ).mulVec (ket T Mod r) = ket T Mod r := by
  ext r'
  simp only [Matrix.mulVec, dotProduct, Rgate, ket, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.sum_apply, Matrix.single, Matrix.of_apply]
  rw [Finset.sum_eq_single r]
  · simp only [↓reduceIte, mul_one]
    have h1 :
        ∑ c' : ΛH, ∑ μ' : ΛG, ∑ Q' : AdBas BH Nminus μ',
          (if regVec T emb μ' Q' c' = r' ∧ regVec T emb μ' Q' c' = r then (1 : ℂ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun c' _ => Finset.sum_eq_zero fun μ' _ =>
        Finset.sum_eq_zero fun Q' _ => ?_
      have hne : regVec T emb μ' Q' c' ≠ r := (hr μ' Q' c').symm
      simp [hne]
    have h2 :
        ∑ c' : ΛH, ∑ μ' : ΛG, ∑ Q' : AdBas BH Nminus μ', ∑ Q'' : AdBas BH Nminus μ',
          (if regVec T emb μ' Q' c' = r' ∧ regVec T emb μ' Q'' c' = r then
            RG μ' (τ : G) Q' Q'' else 0) = 0 := by
      refine Finset.sum_eq_zero fun c' _ => Finset.sum_eq_zero fun μ' _ =>
        Finset.sum_eq_zero fun Q' _ => Finset.sum_eq_zero fun Q'' _ => ?_
      have hne : regVec T emb μ' Q'' c' ≠ r := (hr μ' Q'' c').symm
      simp [hne]
    change (if r' = r then (1 : ℂ) else 0) -
        ∑ c' : ΛH, ∑ μ' : ΛG, ∑ Q' : AdBas BH Nminus μ',
          (if regVec T emb μ' Q' c' = r' ∧ regVec T emb μ' Q' c' = r then (1 : ℂ) else 0) +
        ∑ c' : ΛH, ∑ μ' : ΛG, ∑ Q' : AdBas BH Nminus μ', ∑ Q'' : AdBas BH Nminus μ',
          (if regVec T emb μ' Q' c' = r' ∧ regVec T emb μ' Q'' c' = r then
            RG μ' (τ : G) Q' Q'' else 0) =
      if r' = r then 1 else 0
    rw [h1, h2, sub_zero, add_zero]
  · intro r'' _ hr''; simp [hr'']
  · intro hr''; exact False.elim (hr'' (Finset.mem_univ _))

private theorem rgate_conjTranspose_eq {G : Type} [Group G] [Fintype G] {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {BH : ΛH → Type} [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] {Nminus : ΛG → Finset ΛH} {Mod : Type} [Fintype Mod]
    (emb : ∀ l, BH l → Mod)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (hRG : ∀ μ, IsUnitaryRep (RG μ)) (τ : T) :
    (Rgate T BH Nminus Mod emb RG τ)ᴴ =
      Rgate T BH Nminus Mod emb (fun μ g => RG μ (g⁻¹)) τ := by
  ext r' r
  rw [Matrix.conjTranspose_apply]
  dsimp only [Rgate]
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.one_apply, star_add, star_sub]
  congr 1
  · congr 1
    · split_ifs with h1 h2 h2
      · simp
      · exfalso; exact h2 h1.symm
      · exfalso; exact h1 h2.symm
      · simp
    · rw [Matrix.sum_apply, Matrix.sum_apply, star_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.sum_apply, Matrix.sum_apply, star_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Matrix.sum_apply, Matrix.sum_apply, star_sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      simp only [Matrix.single, Matrix.of_apply]
      split_ifs with h1 h2 h2
      · simp
      · exfalso; exact h2 ⟨h1.2, h1.1⟩
      · exfalso; exact h1 ⟨h2.2, h2.1⟩
      · simp
  · rw [Matrix.sum_apply, Matrix.sum_apply, star_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.sum_apply, Matrix.sum_apply, star_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hlhs :
        star ((∑ Q' : AdBas BH Nminus μ, ∑ Q : AdBas BH Nminus μ,
          Matrix.single (none, (encAd BH Nminus Mod emb μ Q').1, (encAd BH Nminus Mod emb μ Q').2, some μ, c)
            (none, (encAd BH Nminus Mod emb μ Q).1, (encAd BH Nminus Mod emb μ Q).2, some μ, c)
            (RG μ (τ : G) Q' Q)) r r') =
        ∑ Q : AdBas BH Nminus μ, ∑ Q' : AdBas BH Nminus μ,
          star ((Matrix.single (none, (encAd BH Nminus Mod emb μ Q').1, (encAd BH Nminus Mod emb μ Q').2, some μ, c)
            (none, (encAd BH Nminus Mod emb μ Q).1, (encAd BH Nminus Mod emb μ Q).2, some μ, c)
            (RG μ (τ : G) Q' Q)) r r') := by
      rw [Matrix.sum_apply, star_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun Q _ => by rw [Matrix.sum_apply, star_sum]
    have hrhs :
        (∑ Q' : AdBas BH Nminus μ, ∑ Q : AdBas BH Nminus μ,
          Matrix.single (none, (encAd BH Nminus Mod emb μ Q').1, (encAd BH Nminus Mod emb μ Q').2, some μ, c)
            (none, (encAd BH Nminus Mod emb μ Q).1, (encAd BH Nminus Mod emb μ Q).2, some μ, c)
            (RG μ (τ : G)⁻¹ Q' Q)) r' r =
        ∑ Q' : AdBas BH Nminus μ, ∑ Q : AdBas BH Nminus μ,
          (Matrix.single (none, (encAd BH Nminus Mod emb μ Q').1, (encAd BH Nminus Mod emb μ Q').2, some μ, c)
            (none, (encAd BH Nminus Mod emb μ Q).1, (encAd BH Nminus Mod emb μ Q).2, some μ, c)
            (RG μ (τ : G)⁻¹ Q' Q)) r' r := by
      rw [Matrix.sum_apply]
      refine Finset.sum_congr rfl fun Q' _ => Matrix.sum_apply _ _ _ _
    rw [hlhs, hrhs]
    refine Finset.sum_congr rfl fun Q' _ => Finset.sum_congr rfl fun Q _ => ?_
    have hinv : RG μ (τ : G)⁻¹ Q' Q = star (RG μ (τ : G) Q Q') := by
      rw [isUnitaryRep_inv_eq_conjTranspose (hRG μ) (τ : G), Matrix.conjTranspose_apply]
    simp only [Matrix.single, Matrix.of_apply]
    by_cases h1 : (none, (encAd BH Nminus Mod emb μ Q).1, (encAd BH Nminus Mod emb μ Q).2, some μ, c) = r ∧
        (none, (encAd BH Nminus Mod emb μ Q').1, (encAd BH Nminus Mod emb μ Q').2, some μ, c) = r'
    · rw [if_pos h1, if_pos ⟨h1.2, h1.1⟩]
      exact hinv.symm
    · have h2 : ¬((none, (encAd BH Nminus Mod emb μ Q').1, (encAd BH Nminus Mod emb μ Q').2, some μ, c) = r' ∧
          (none, (encAd BH Nminus Mod emb μ Q).1, (encAd BH Nminus Mod emb μ Q).2, some μ, c) = r) :=
        fun ⟨a, b⟩ => h1 ⟨b, a⟩
      rw [if_neg h1, if_neg h2, star_zero]

private theorem rgate_mul_conjTranspose {G : Type} [Group G] [Fintype G] {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {BH : ΛH → Type} [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] {Nminus : ΛG → Finset ΛH} {Mod : Type} [Fintype Mod]
    (emb : ∀ l, BH l → Mod) (hemb : ∀ l, Function.Injective (emb l))
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (hRG : ∀ μ, IsUnitaryRep (RG μ)) (τ : T) :
    Rgate T BH Nminus Mod emb RG τ * (Rgate T BH Nminus Mod emb RG τ)ᴴ = 1 := by
  suffices h : ∀ r, (Rgate T BH Nminus Mod emb RG τ * (Rgate T BH Nminus Mod emb RG τ)ᴴ).mulVec
      (ket T Mod r) = ket T Mod r by
    ext r' r
    have hev := congr_fun (h r) r'
    have hket : ∀ (M : Matrix (Reg T Mod) (Reg T Mod) ℂ),
        (M.mulVec (ket T Mod r)) r' = M r' r := fun M => by
      simp [Matrix.mulVec, dotProduct, ket]
    rw [hket] at hev
    simpa [ket, Matrix.one_apply] using hev
  intro r
  rw [← Matrix.mulVec_mulVec, rgate_conjTranspose_eq emb RG hRG τ]
  by_cases hex : ∃ (μ : ΛG) (Q : AdBas BH Nminus μ) (c : ΛH), r = regVec T emb μ Q c
  · rcases hex with ⟨μ, Q, c, rfl⟩
    rw [rgate_mulVec_ket_vec emb hemb _ τ μ Q c, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, rgate_mulVec_ket_vec emb hemb RG τ]
    have hswap :
        ∑ Q' : AdBas BH Nminus μ, RG μ (τ : G)⁻¹ Q' Q •
          ∑ Q'' : AdBas BH Nminus μ, RG μ (τ : G) Q'' Q' • ket T Mod (regVec T emb μ Q'' c) =
        ∑ Q'' : AdBas BH Nminus μ,
          (∑ Q' : AdBas BH Nminus μ, RG μ (τ : G) Q'' Q' * RG μ (τ : G)⁻¹ Q' Q) •
            ket T Mod (regVec T emb μ Q'' c) := by
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun Q'' _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl fun Q' _ => by rw [mul_comm]
    rw [hswap]
    have hprod : ∀ Q'',
        ∑ Q' : AdBas BH Nminus μ, RG μ (τ : G) Q'' Q' * RG μ (τ : G)⁻¹ Q' Q =
          if Q'' = Q then 1 else 0 := fun Q'' => by
      rw [← Matrix.mul_apply, ← (hRG μ).1.2, mul_inv_cancel, (hRG μ).1.1, Matrix.one_apply]
    simp only [hprod, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · push Not at hex
    rw [rgate_mulVec_ket_not_vec emb _ τ r hex, rgate_mulVec_ket_not_vec emb RG τ r hex]

private theorem ugate_conjTranspose_eq {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {Mod : Type} [Fintype Mod]
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) :
    (Ugate T Mod Ul)ᴴ = Ugate T Mod (fun l => (Ul l)ᴴ) := by
  ext r' r
  simp only [Ugate, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hr : r.1 = none <;> by_cases hr' : r'.1 = none
  · simp only [hr, hr', ↓reduceIte, true_and]
    by_cases h1 : r'.2.1 = r.2.1 ∧ r'.2.2.1 = r.2.2.1 ∧ r'.2.2.2.2 = r.2.2.2.2
    · have h2 : r.2.1 = r'.2.1 ∧ r.2.2.1 = r'.2.2.1 ∧ r.2.2.2.2 = r'.2.2.2.2 :=
        ⟨h1.1.symm, h1.2.1.symm, h1.2.2.symm⟩
      rw [if_pos h1, if_pos h2, h1.2.2]
    · have h2 : ¬(r.2.1 = r'.2.1 ∧ r.2.2.1 = r'.2.2.1 ∧ r.2.2.2.2 = r'.2.2.2.2) := fun h =>
        h1 ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
      rw [if_neg h1, if_neg h2, star_zero]
  · have hne : r ≠ r' := fun h => hr' (by rw [← h]; exact hr)
    simp [hr, hr', hne]
  · have hne : r' ≠ r := fun h => hr (by rw [← h]; exact hr')
    simp [hr, hr', hne]
  · simp [hr, hr', eq_comm]

private theorem ugate_mul_conjTranspose {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {BH : ΛH → Type} [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] {Nminus : ΛG → Finset ΛH} {Mod : Type} [Fintype Mod]
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) (hUl : IsAdmissibleU T BH Nminus Ul) :
    Ugate T Mod Ul * (Ugate T Mod Ul)ᴴ = 1 := by
  rw [ugate_conjTranspose_eq]
  ext r' r
  simp only [Matrix.mul_apply, Ugate, Matrix.of_apply, Matrix.one_apply]
  by_cases hr : r.1 = none
  · rcases r with ⟨r1, m, lh, lg, c⟩
    dsimp at hr
    subst hr
    by_cases hr' : r'.1 = none
    · rcases r' with ⟨r'1, m', lh', lg', c'⟩
      dsimp at hr'
      subst hr'
      have hsum :
          ∑ x : Reg T Mod,
            (if x.1 = none then
              if (none : Option T) = none ∧ m' = x.2.1 ∧ lh' = x.2.2.1 ∧ c' = x.2.2.2.2 then
                Ul x.2.2.2.2 lg' x.2.2.2.1 else 0
            else if (none, m', lh', lg', c') = x then 1 else 0) *
            (if (none : Option T) = none then
              if x.1 = none ∧ x.2.1 = m ∧ x.2.2.1 = lh ∧ x.2.2.2.2 = c then (Ul c)ᴴ x.2.2.2.1 lg else 0
            else if x = (none, m, lh, lg, c) then 1 else 0) =
          if m' = m ∧ lh' = lh ∧ c' = c then
            ∑ xlg : Option ΛG, Ul c lg' xlg * (Ul c)ᴴ xlg lg
          else 0 := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single (none : Option T)]
        · simp only [↓reduceIte, true_and]
          rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
          · rw [Fintype.sum_prod_type, Finset.sum_eq_single lh]
            · rw [Fintype.sum_prod_type]
              by_cases hcond : m' = m ∧ lh' = lh ∧ c' = c
              · rcases hcond with ⟨hm, hlh, hc⟩
                subst hm hlh hc
                rw [if_pos ⟨rfl, rfl, rfl⟩]
                refine Finset.sum_congr rfl fun xlg _ => ?_
                rw [Finset.sum_eq_single c']
                · simp
                · intro xc _ hxc; simp [hxc.symm]
                · intro hc; exact False.elim (hc (Finset.mem_univ _))
              · rw [if_neg hcond]
                refine Finset.sum_eq_zero fun xlg _ => Finset.sum_eq_zero fun xc _ => ?_
                by_cases hxc : xc = c
                · subst hxc; simp [hcond]
                · simp [hxc]
            · intro xlh _ hxlh; simp [hxlh]
            · intro hlh; exact False.elim (hlh (Finset.mem_univ _))
          · intro xm _ hxm; simp [hxm]
          · intro hm; exact False.elim (hm (Finset.mem_univ _))
        · intro x1 _ hx1; simp [hx1]
        · intro hnone; exact False.elim (hnone (Finset.mem_univ _))
      have hunit : ∑ xlg : Option ΛG, Ul c lg' xlg * (Ul c)ᴴ xlg lg = if lg' = lg then 1 else 0 := by
        have := Matrix.mem_unitaryGroup_iff.mp (hUl c).1
        rw [Matrix.star_eq_conjTranspose] at this
        have he := congr_fun (congr_fun this lg') lg
        simpa [Matrix.mul_apply, Matrix.one_apply] using he
      rw [hsum, hunit]
      by_cases hm : m' = m <;> by_cases hlh : lh' = lh <;> by_cases hlg : lg' = lg <;> by_cases hc : c' = c <;>
        simp [hm, hlh, hlg, hc]
    · rw [Finset.sum_eq_zero]
      · have hne : r' ≠ (none, m, lh, lg, c) := fun h => hr' (by rw [h])
        simp [hne]
      · intro x _
        by_cases hx : x.1 = none
        · simp [hx, hr']
        · simp [hx]
  · rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro x _ hx
      simp [hr, hx]
    · intro hr''; exact False.elim (hr'' (Finset.mem_univ _))

private theorem ugate_mulVec_ket_some {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {Mod : Type} [Fintype Mod]
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ)
    (r : Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) (hr : r.1 ≠ none) :
    (Ugate T Mod Ul).mulVec (ket T Mod r) = ket T Mod r := by
  ext r'
  simp only [Matrix.mulVec, dotProduct, Ugate, ket, Matrix.of_apply]
  rw [Finset.sum_eq_single r]
  · simp [hr, eq_comm]
  · intro x _ hx; simp [hx]
  · intro hr''; exact False.elim (hr'' (Finset.mem_univ _))

private theorem ugate_mulVec_ket_none {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {Mod : Type} [Fintype Mod]
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ)
    (m : Mod) (lh : Option ΛH) (lg : Option ΛG) (c : ΛH) :
    (Ugate T Mod Ul).mulVec (ket T Mod (none, m, lh, lg, c)) =
      ∑ lg' : Option ΛG, (Ul c lg' lg) • ket T Mod (none, m, lh, lg', c) := by
  ext r'
  simp only [Matrix.mulVec, dotProduct, Ugate, ket, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (none, m, lh, lg, c)]
  · simp only [↓reduceIte, mul_one]
    split_ifs with h
    · rcases r' with ⟨r'1, m', lh', lg', c'⟩
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      rw [Finset.sum_eq_single lg']
      · simp
      · intro x _ hx; simp [hx.symm]
      · intro hx; exact False.elim (hx (Finset.mem_univ _))
    · rw [Finset.sum_eq_zero]
      intro x _
      have hne : r' ≠ (none, m, lh, x, c) := fun heq => by
        apply h
        rw [heq]
        simp
      simp [hne]
  · intro x _ hx; simp [hx]
  · intro hx; exact False.elim (hx (Finset.mem_univ _))

private theorem ugate_conjTranspose_mulVec_apply_some {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {Mod : Type} [Fintype Mod]
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ)
    (v : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ)
    (r' : Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) (hr' : r'.1 ≠ none) :
    ((Ugate T Mod Ul)ᴴ.mulVec v) r' = v r' := by
  rw [ugate_conjTranspose_eq]
  simp only [Matrix.mulVec, dotProduct, Ugate, Matrix.of_apply]
  rw [Finset.sum_eq_single r']
  · simp [hr']
  · intro r _ hr
    by_cases hr1 : r.1 = none
    · simp [hr1, hr']
    · simp [hr1, hr.symm]
  · intro hr''; exact False.elim (hr'' (Finset.mem_univ _))

private theorem ugate_conjTranspose_mulVec_apply_none {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {Mod : Type} [Fintype Mod]
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ)
    (v : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ)
    (m : Mod) (lh : Option ΛH) (lg : Option ΛG) (c : ΛH) :
    ((Ugate T Mod Ul)ᴴ.mulVec v) (none, m, lh, lg, c) =
      ∑ lg' : Option ΛG, star (Ul c lg' lg) * v (none, m, lh, lg', c) := by
  rw [ugate_conjTranspose_eq]
  simp only [Matrix.mulVec, dotProduct, Ugate, Matrix.of_apply]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (none : Option T)]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single lh]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun lg' _ => ?_
        rw [Finset.sum_eq_single c]
        · simp [Matrix.conjTranspose_apply]
        · intro c' _ hc'; simp [hc'.symm]
        · intro hc; exact False.elim (hc (Finset.mem_univ _))
      · intro lh' _ hlh'
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [hlh'.symm]
      · intro hlh; exact False.elim (hlh (Finset.mem_univ _))
    · intro m' _ hm'
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [hm'.symm]
    · intro hm; exact False.elim (hm (Finset.mem_univ _))
  · intro r1 _ hr1
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [hr1, hr1.symm]
  · intro hr1; exact False.elim (hr1 (Finset.mem_univ _))

private theorem vgate_mulVec_ket_swap_to_none {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {Mod : Type} [Fintype Mod]
    (τ : T) (m : Mod) (c : ΛH) :
    (Vgate T Mod (ΛH := ΛH) (ΛG := ΛG) τ).mulVec
        (ket T Mod (ΛH := ΛH) (ΛG := ΛG) (some τ, m, some c, none, c)) =
      ket T Mod (ΛH := ΛH) (ΛG := ΛG) (none, m, some c, none, c) := by
  ext r'
  simp only [Matrix.mulVec, dotProduct, Vgate, Xk, ket, Matrix.of_apply]
  rw [Finset.sum_eq_single (some τ, m, some c, none, c)]
  · simp only [↓reduceIte, mul_one]
    by_cases hr' : r'.2 = (m, some c, none, c)
    · rcases r' with ⟨r'1, r'2⟩
      dsimp at hr'
      subst hr'
      simp [Prod.mk.injEq]
    · have hne : r' ≠ (none, m, some c, none, c) := fun h => hr' (by rw [h])
      simp [hr', hne]
  · intro r _ hr; simp [hr]
  · intro hr; exact False.elim (hr (Finset.mem_univ _))

private theorem vgate_mulVec_ket_other {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {Mod : Type} [Fintype Mod]
    (τ τ' : T) (hne : τ' ≠ τ) (m : Mod) (c : ΛH) :
    (Vgate T Mod (ΛH := ΛH) (ΛG := ΛG) τ).mulVec
        (ket T Mod (ΛH := ΛH) (ΛG := ΛG) (some τ', m, some c, none, c)) =
      ket T Mod (ΛH := ΛH) (ΛG := ΛG) (some τ', m, some c, none, c) := by
  ext r'
  simp only [Matrix.mulVec, dotProduct, Vgate, Xk, ket, Matrix.of_apply]
  rw [Finset.sum_eq_single (some τ', m, some c, none, c)]
  · simp only [↓reduceIte, mul_one]
    by_cases hr' : r'.2 = (m, some c, none, c)
    · rcases r' with ⟨r'1, r'2⟩
      dsimp at hr'
      subst hr'
      simp [hne, Prod.mk.injEq]
    · have hne' : r' ≠ (some τ', m, some c, none, c) := fun h => hr' (by rw [h])
      simp [hr', hne']
  · intro r _ hr; simp [hr]
  · intro hr; exact False.elim (hr (Finset.mem_univ _))

private theorem vgate_mulVec_eq_self_of_vanish {G : Type} {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {Mod : Type} [Fintype Mod]
    (τ : T) (w : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ)
    (hw : ∀ (m : Mod) (c : ΛH),
      w (none, m, some c, none, c) = 0 ∧ w (some τ, m, some c, none, c) = 0) :
    (Vgate T Mod τ).mulVec w = w := by
  ext r'
  simp only [Matrix.mulVec, dotProduct, Vgate, Xk, Matrix.of_apply]
  by_cases hctrl : r'.2.2.2.1 = none ∧ r'.2.2.1 = some r'.2.2.2.2
  · rcases r' with ⟨r'1, m', lh', lg', c'⟩
    dsimp at hctrl
    rcases hctrl with ⟨rfl, rfl⟩
    by_cases hr1 : r'1 = none ∨ r'1 = some τ
    · have hw_lhs : w (r'1, m', some c', none, c') = 0 := by
        rcases hr1 with rfl | rfl
        · exact (hw m' c').1
        · exact (hw m' c').2
      rw [hw_lhs]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hrc : r.2.2.2.1 = none ∧ r.2.2.1 = some r.2.2.2.2
      · by_cases hr2 : (m', some c', none, c') = r.2
        · rcases r with ⟨r1, r2⟩
          dsimp at hr2
          subst hr2
          rcases hr1 with rfl | rfl
          · by_cases hr1' : r1 = some τ
            · subst hr1'; simp [(hw m' c').2]
            · by_cases hr1'' : r1 = none
              · subst hr1''; simp
              · simp [hr1', hr1'', Ne.symm hr1'']
          · by_cases hr1' : r1 = none
            · subst hr1'; simp [(hw m' c').1]
            · by_cases hr1'' : r1 = some τ
              · subst hr1''; simp
              · simp [hr1', hr1'', Ne.symm hr1'']
        · simp [hrc, hr2]
      · have hne : (r'1, m', some c', none, c') ≠ r := fun h => hrc (by rw [← h]; exact ⟨rfl, rfl⟩)
        simp [hrc, hne]
    · push Not at hr1
      rw [Finset.sum_eq_single (r'1, m', some c', none, c')]
      · simp [hr1.1, hr1.2]
      · intro r _ hr
        by_cases hrc : r.2.2.2.1 = none ∧ r.2.2.1 = some r.2.2.2.2
        · by_cases hr2 : (m', some c', none, c') = r.2
          · rcases r with ⟨r1, r2⟩
            dsimp at hr2
            subst hr2
            have hr1_ne : r'1 ≠ r1 := fun h => hr (by subst h; rfl)
            by_cases ha : r1 = none
            · subst ha; simp [hr1.2]
            · by_cases hb : r1 = some τ
              · subst hb; simp [hr1.1]
              · simp [ha, hb, hr1_ne]
          · simp [hrc, hr2]
        · have hne : (r'1, m', some c', none, c') ≠ r := fun h => hr (by rw [h])
          simp [hrc, hne]
      · intro hr'; exact False.elim (hr' (Finset.mem_univ _))
  · rw [Finset.sum_eq_single r']
    · simp [hctrl]
    · intro r _ hr
      by_cases hrc : r.2.2.2.1 = none ∧ r.2.2.1 = some r.2.2.2.2
      · have hr2 : r'.2 ≠ r.2 := fun h => hctrl (by rw [h]; exact hrc)
        simp [hrc, hr2]
      · simp [hrc, hr.symm]
    · intro hr'; exact False.elim (hr' (Finset.mem_univ _))

private theorem wgate_fix_input {G : Type} [Group G] [Fintype G] {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {BH : ΛH → Type} [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] {Nminus : ΛG → Finset ΛH} {Mod : Type} [Fintype Mod]
    (emb : ∀ l, BH l → Mod)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (hRG : ∀ μ, IsUnitaryRep (RG μ))
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ)
    {τ₁ τ₂ : T} (hne : τ₁ ≠ τ₂) (l : ΛH) (P : BH l) :
    (Wgate T BH Nminus Mod emb RG Ul τ₂).mulVec
        (ket T Mod (ΛH := ΛH) (ΛG := ΛG) (some τ₁, emb l P, some l, none, l)) =
      ket T Mod (ΛH := ΛH) (ΛG := ΛG) (some τ₁, emb l P, some l, none, l) := by
  let v₀ : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ :=
    ket T Mod (some τ₁, emb l P, some l, none, l)
  have hnot : ∀ (μ : ΛG) (Q : AdBas BH Nminus μ) (c : ΛH),
      (some τ₁, emb l P, some l, none, l) ≠ regVec T emb μ Q c := by
    intro μ Q c h
    cases congrArg (fun r : Reg T Mod => r.1) h
  have h1 : (Rgate T BH Nminus Mod emb RG τ₂)ᴴ.mulVec v₀ = v₀ := by
    rw [rgate_conjTranspose_eq emb RG hRG τ₂]
    exact rgate_mulVec_ket_not_vec emb _ τ₂ _ hnot
  have h2 : (Ugate T Mod Ul)ᴴ.mulVec v₀ = v₀ := by
    rw [ugate_conjTranspose_eq]
    exact ugate_mulVec_ket_some _ _ (by simp)
  have h3 : (Vgate T Mod τ₂).mulVec v₀ = v₀ :=
    vgate_mulVec_ket_other τ₂ τ₁ hne (emb l P) l
  have h4 : (Ugate T Mod Ul).mulVec v₀ = v₀ :=
    ugate_mulVec_ket_some Ul _ (by simp)
  have h5 : (Rgate T BH Nminus Mod emb RG τ₂).mulVec v₀ = v₀ :=
    rgate_mulVec_ket_not_vec emb RG τ₂ _ hnot
  simp only [Wgate, ← Matrix.mulVec_mulVec]
  rw [h1, h2, h3, h4, h5]

private theorem wgate_step_k {G : Type} [Group G] [Fintype G] {T : Set G} [Fintype T]
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] {BH : ΛH → Type} [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] {Nminus : ΛG → Finset ΛH} {Mod : Type} [Fintype Mod]
    (emb : ∀ l, BH l → Mod) (hemb : ∀ l, Function.Injective (emb l))
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (hRG : ∀ μ, IsUnitaryRep (RG μ))
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) (hUl : IsAdmissibleU T BH Nminus Ul)
    (τk : T) (l : ΛH) (P : BH l) :
    (Wgate T BH Nminus Mod emb RG Ul τk).mulVec
        (ket T Mod (ΛH := ΛH) (ΛG := ΛG) (some τk, emb l P, some l, none, l)) =
      bealsTarget T BH Nminus Mod emb RG τk l P := by
  let v₀ : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ :=
    ket T Mod (some τk, emb l P, some l, none, l)
  have hnot : ∀ (μ : ΛG) (Q : AdBas BH Nminus μ) (c : ΛH),
      (some τk, emb l P, some l, none, l) ≠ regVec T emb μ Q c := by
    intro μ Q c h
    cases congrArg (fun r : Reg T Mod => r.1) h
  have h1 : (Rgate T BH Nminus Mod emb RG τk)ᴴ.mulVec v₀ = v₀ := by
    rw [rgate_conjTranspose_eq emb RG hRG τk]
    exact rgate_mulVec_ket_not_vec emb _ τk _ hnot
  have h2 : (Ugate T Mod Ul)ᴴ.mulVec v₀ = v₀ := by
    rw [ugate_conjTranspose_eq]
    exact ugate_mulVec_ket_some _ _ (by simp)
  have h3 : (Vgate T Mod τk).mulVec v₀ = ket T Mod (none, emb l P, some l, none, l) :=
    vgate_mulVec_ket_swap_to_none τk (emb l P) l
  have h4 : (Ugate T Mod Ul).mulVec (ket T Mod (none, emb l P, some l, none, l)) =
      ∑ μ : ΛG, if h : l ∈ Nminus μ then
        (Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l)) : ℂ) •
          ket T Mod (regVec T emb μ ⟨⟨l, h⟩, P⟩ l)
      else 0 := by
    rw [ugate_mulVec_ket_none Ul (emb l P) (some l) none l]
    have hphi : ∀ m : Option ΛG, Ul l m none = phi T BH Nminus l m := (hUl l).2
    simp_rw [hphi]
    rw [Fintype.sum_option]
    simp only [phi, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs with h
    · rfl
    · simp
  simp only [Wgate, ← Matrix.mulVec_mulVec]
  rw [h1, h2, h3, h4, Matrix.mulVec_sum]
  simp only [bealsTarget]
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs with h
  · rw [Matrix.mulVec_smul, rgate_mulVec_ket_vec emb hemb RG τk μ ⟨⟨l, h⟩, P⟩ l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [smul_smul]
    rfl
  · simp

private theorem wgate_fix_target {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H]
    (T : Set G) [Fintype T] (hT : Subgroup.IsComplement T (H : Set G)) (he : (1 : G) ∈ T)
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG)
    {Mod : Type} [Fintype Mod] (emb : ∀ l, BH l → Mod) (hemb : ∀ l, Function.Injective (emb l))
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) (hUl : IsAdmissibleU T BH Nminus Ul)
    {τj τk : T} (hne : τj ≠ τk) (l : ΛH) (P : BH l) :
    (Wgate T BH Nminus Mod emb RG Ul τj).mulVec (bealsTarget T BH Nminus Mod emb RG τk l P) =
      bealsTarget T BH Nminus Mod emb RG τk l P := by
  let t := bealsTarget T BH Nminus Mod emb RG τk l P
  let v₁ := (Rgate T BH Nminus Mod emb RG τj)ᴴ.mulVec t
  have hv₁_eq : v₁ =
      ∑ μ : ΛG, ∑ Q' : AdBas BH Nminus μ,
        if h : l ∈ Nminus μ then
          ((Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l)) : ℂ) *
            RG μ ((τj : G)⁻¹ * (τk : G)) Q' ⟨⟨l, h⟩, P⟩) •
          ket T Mod (regVec T emb μ Q' l)
        else 0 := by
    dsimp [v₁, t, bealsTarget]
    rw [rgate_conjTranspose_eq emb RG hRG.1 τj, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Matrix.mulVec_sum]
    by_cases h : l ∈ Nminus μ
    · have hket : ∀ Q : AdBas BH Nminus μ,
          (none, emb Q.1.1 Q.2, some Q.1.1, some μ, l) = regVec T emb μ Q l := fun _ => rfl
      simp_rw [dif_pos h, hket, Matrix.mulVec_smul,
        rgate_mulVec_ket_vec emb hemb (fun μ g => RG μ g⁻¹) τj μ _ l]
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun Q' _ => ?_
      have hmul :
          ∑ Q : AdBas BH Nminus μ,
            ((Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l)) : ℂ) *
              RG μ (τk : G) Q ⟨⟨l, h⟩, P⟩) *
            RG μ (τj : G)⁻¹ Q' Q =
          (Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l)) : ℂ) *
            RG μ ((τj : G)⁻¹ * (τk : G)) Q' ⟨⟨l, h⟩, P⟩ := by
        rw [(hRG.1 μ).1.2 (τj : G)⁻¹ (τk : G), Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun Q _ => by ring
      rw [← Finset.sum_smul, hmul]
    · simp [h]
  have hvanish : ∀ (m : Mod) (c : ΛH),
      ((Ugate T Mod Ul)ᴴ.mulVec v₁) (none, m, some c, none, c) = 0 ∧
      ((Ugate T Mod Ul)ᴴ.mulVec v₁) (some τj, m, some c, none, c) = 0 := by
    intro m c
    constructor
    · rw [ugate_conjTranspose_mulVec_apply_none Ul v₁ m (some c) none c]
      rw [Fintype.sum_option]
      have hv1_none : v₁ (none, m, some c, none, c) = 0 := by
        rw [hv₁_eq]
        simp only [Finset.sum_apply]
        refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun Q' _ => ?_
        split_ifs <;> simp [ket, regVec]
      rw [hv1_none, mul_zero, zero_add]
      have hterm_μ : ∀ μ : ΛG,
          star (Ul c (some μ) none) * v₁ (none, m, some c, some μ, c) =
            if hc : c = l then
              if h : l ∈ Nminus μ then
                if hQ : ∃ Q₀ : BH l, emb l Q₀ = m then
                  ((dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l) : ℝ) : ℂ) *
                    RG μ ((τj : G)⁻¹ * (τk : G)) ⟨⟨l, h⟩, hQ.choose⟩ ⟨⟨l, h⟩, P⟩
                else 0
              else 0
            else 0 := by
        intro μ
        have hul_val : star (Ul c (some μ) none) =
            if hc' : c ∈ Nminus μ then
              (Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH c)) : ℂ)
            else 0 := by
          rw [(hUl c).2 (some μ)]
          simp only [phi]
          split_ifs <;> simp
        have hv1_val : v₁ (none, m, some c, some μ, c) =
            if hc : c = l then
              if h : l ∈ Nminus μ then
                if hQ : ∃ Q₀ : BH l, emb l Q₀ = m then
                  (Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l)) : ℂ) *
                    RG μ ((τj : G)⁻¹ * (τk : G)) ⟨⟨l, h⟩, hQ.choose⟩ ⟨⟨l, h⟩, P⟩
                else 0
              else 0
            else 0 := by
          rw [hv₁_eq]
          simp only [Finset.sum_apply]
          rw [Finset.sum_eq_single μ]
          · by_cases hc : c = l
            · rcases hc with rfl
              rw [dif_pos rfl]
              by_cases h : c ∈ Nminus μ
              · simp only [dif_pos h, Pi.smul_apply, smul_eq_mul]
                by_cases hQ : ∃ Q₀ : BH c, emb c Q₀ = m
                · rw [dif_pos hQ, Finset.sum_eq_single ⟨⟨c, h⟩, hQ.choose⟩]
                  · simp [ket, regVec, encAd, hQ.choose_spec]
                  · intro Q' _ hQ'
                    have hne_ket : regVec T emb μ Q' c ≠ (none, m, some c, some μ, c) := by
                      intro heq
                      apply hQ'
                      have hl1 : Q'.1.1 = c := Option.some.inj (congrArg (fun r : Reg T Mod => r.2.2.1) heq)
                      have hm1 : emb Q'.1.1 Q'.2 = m := congrArg (fun r : Reg T Mod => r.2.1) heq
                      rcases Q' with ⟨⟨l', hl'⟩, P'⟩
                      dsimp at hl1 hm1
                      subst hl1
                      have := hemb _ (hm1.trans hQ.choose_spec.symm)
                      subst this
                      rfl
                    simp [ket, hne_ket.symm]
                  · intro hmem; exact False.elim (hmem (Finset.mem_univ _))
                · rw [dif_neg hQ]
                  refine Finset.sum_eq_zero fun Q' _ => ?_
                  have hne_ket : regVec T emb μ Q' c ≠ (none, m, some c, some μ, c) := by
                    intro heq
                    apply hQ
                    have hl1 : Q'.1.1 = c := Option.some.inj (congrArg (fun r : Reg T Mod => r.2.2.1) heq)
                    have hm1 : emb Q'.1.1 Q'.2 = m := congrArg (fun r : Reg T Mod => r.2.1) heq
                    rcases Q' with ⟨⟨l', hl'⟩, P'⟩
                    dsimp at hl1 hm1
                    subst hl1
                    exact ⟨P', hm1⟩
                  simp [ket, hne_ket.symm]
              · simp [h]
            · simp only [dif_neg hc]
              refine Finset.sum_eq_zero fun Q' _ => ?_
              split_ifs with h
              · have hne_ket : regVec T emb μ Q' l ≠ (none, m, some c, some μ, c) := by
                  intro heq
                  exact hc (congrArg (fun r : Reg T Mod => r.2.2.2.2) heq).symm
                simp [ket, hne_ket.symm]
              · simp
          · intro μ' _ hμ'
            refine Finset.sum_eq_zero fun Q' _ => ?_
            split_ifs with h
            · have hne_ket : regVec T emb μ' Q' l ≠ (none, m, some c, some μ, c) := by
                intro heq
                exact hμ' (Option.some.inj (congrArg (fun r : Reg T Mod => r.2.2.2.1) heq))
              simp [ket, hne_ket.symm]
            · simp
          · intro hμ; exact False.elim (hμ (Finset.mem_univ _))
        rw [hul_val, hv1_val]
        by_cases hc : c = l
        · rcases hc with rfl
          rw [dif_pos rfl, dif_pos rfl]
          by_cases h : c ∈ Nminus μ
          · rw [dif_pos h, dif_pos h, dif_pos h]
            by_cases hQ : ∃ Q₀ : BH c, emb c Q₀ = m
            · rw [dif_pos hQ, dif_pos hQ]
              have hsq :
                  (Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH c)) : ℂ) *
                  (Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH c)) : ℂ) =
                  ((dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH c) : ℝ) : ℂ) := by
                rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
              rw [← mul_assoc, hsq]
            · rw [dif_neg hQ, dif_neg hQ, mul_zero]
          · rw [dif_neg h, dif_neg h, dif_neg h, zero_mul]
        · rw [dif_neg hc, dif_neg hc, mul_zero]
      simp_rw [hterm_μ]
      by_cases hc : c = l
      · rcases hc with rfl
        by_cases hQ : ∃ Q₀ : BH c, emb c Q₀ = m
        · have hclean :
              (∑ μ : ΛG, if hc : c = c then
                if h : c ∈ Nminus μ then
                  if hQ' : ∃ Q₀ : BH c, emb c Q₀ = m then
                    ((dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH c) : ℝ) : ℂ) *
                      RG μ ((τj : G)⁻¹ * (τk : G)) ⟨⟨c, h⟩, hQ'.choose⟩ ⟨⟨c, h⟩, P⟩
                  else 0
                else 0
              else 0) =
              ∑ μ : ΛG, if h : c ∈ Nminus μ then
                ((dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH c) : ℝ) : ℂ) *
                  RG μ ((τj : G)⁻¹ * (τk : G)) ⟨⟨c, h⟩, hQ.choose⟩ ⟨⟨c, h⟩, P⟩
              else 0 := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            rw [dif_pos rfl]
            by_cases h : c ∈ Nminus μ
            · rw [dif_pos h, dif_pos h, dif_pos hQ]
            · rw [dif_neg h, dif_neg h]
          rw [hclean]
          have hg_not_mem : ((τj : G)⁻¹ * (τk : G)) ∉ H := by
            intro hm
            let e : T × H ≃ G := Equiv.ofBijective _ hT
            have heq_mul : e (τj, ⟨(τj : G)⁻¹ * (τk : G), hm⟩) = e (τk, 1) := by
              change (τj : G) * ((τj : G)⁻¹ * (τk : G)) = (τk : G) * (1 : G)
              rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one]
            exact hne (congrArg Prod.fst (e.injective heq_mul))
          exact lemma_4_2_not_mem H T hT he BH Nminus RH hRH RG hRG hAd hg_not_mem c hQ.choose P
        · refine Finset.sum_eq_zero fun μ _ => ?_
          rw [dif_pos rfl]
          by_cases h : c ∈ Nminus μ
          · rw [dif_pos h, dif_neg hQ]
          · rw [dif_neg h]
      · refine Finset.sum_eq_zero fun μ _ => by rw [dif_neg hc]
    · rw [ugate_conjTranspose_mulVec_apply_some Ul v₁ _ (by simp)]
      rw [hv₁_eq]
      simp only [Finset.sum_apply]
      refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun Q' _ => ?_
      split_ifs <;> simp [ket, regVec]
  have hUVU : (Ugate T Mod Ul * Vgate T Mod τj * (Ugate T Mod Ul)ᴴ).mulVec v₁ = v₁ := by
    have hV : (Vgate T Mod τj).mulVec ((Ugate T Mod Ul)ᴴ.mulVec v₁) = (Ugate T Mod Ul)ᴴ.mulVec v₁ :=
      vgate_mulVec_eq_self_of_vanish τj _ hvanish
    calc (Ugate T Mod Ul * Vgate T Mod τj * (Ugate T Mod Ul)ᴴ).mulVec v₁
        = (Ugate T Mod Ul).mulVec ((Vgate T Mod τj).mulVec ((Ugate T Mod Ul)ᴴ.mulVec v₁)) := by
          simp only [← Matrix.mulVec_mulVec]
      _ = (Ugate T Mod Ul).mulVec ((Ugate T Mod Ul)ᴴ.mulVec v₁) := by rw [hV]
      _ = (Ugate T Mod Ul * (Ugate T Mod Ul)ᴴ).mulVec v₁ := Matrix.mulVec_mulVec _ _ _
      _ = v₁ := by rw [ugate_mul_conjTranspose Ul hUl, Matrix.one_mulVec]
  calc (Wgate T BH Nminus Mod emb RG Ul τj).mulVec t
      = (Rgate T BH Nminus Mod emb RG τj).mulVec
          ((Ugate T Mod Ul * Vgate T Mod τj * (Ugate T Mod Ul)ᴴ).mulVec v₁) := by
        simp only [Wgate, v₁, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    _ = (Rgate T BH Nminus Mod emb RG τj).mulVec v₁ := by rw [hUVU]
    _ = (Rgate T BH Nminus Mod emb RG τj * (Rgate T BH Nminus Mod emb RG τj)ᴴ).mulVec t := by
        simp only [v₁, Matrix.mulVec_mulVec]
    _ = t := by rw [rgate_mul_conjTranspose emb hemb RG hRG.1 τj, Matrix.one_mulVec]

end GL2QFT.Supplement.BealsProof

open GL2QFT.Supplement.BealsProof in
theorem solution {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] (T : Set G)
    [Fintype T] (hT : Subgroup.IsComplement T (H : Set G)) (he : (1 : G) ∈ T)
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG)
    (Mod : Type) [Fintype Mod] (emb : ∀ l, BH l → Mod) (hemb : ∀ l, Function.Injective (emb l))
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) (hUl : IsAdmissibleU T BH Nminus Ul)
    (τ : Fin (Fintype.card T) ≃ T) (k : Fin (Fintype.card T)) (l : ΛH) (P : BH l) :
    (Wprod T BH Nminus Mod emb RG Ul τ).mulVec (ket T Mod (some (τ k), emb l P, some l, none, l)) =
      bealsTarget T BH Nminus Mod emb RG (τ k) l P := by
  let n := Fintype.card T
  let f : Fin n → Matrix (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) ℂ :=
    fun i => Wgate T BH Nminus Mod emb RG Ul (τ i.rev)
  let v₀ : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ :=
    ket T Mod (some (τ k), emb l P, some l, none, l)
  let tgt : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ :=
    bealsTarget T BH Nminus Mod emb RG (τ k) l P
  have hfix_in : ∀ (L : List (Fin n)), k.rev ∉ L → (L.map f).prod.mulVec v₀ = v₀ := by
    intro L hL
    induction L with
    | nil => simp
    | cons a as ih =>
      have ha : a ≠ k.rev := fun h => hL (by simp [h])
      have has : k.rev ∉ as := fun h => hL (by simp [h])
      have harev : τ k ≠ τ a.rev := fun heq => ha (by
        have : k = a.rev := τ.injective heq
        rw [this, Fin.rev_rev])
      simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
      rw [ih has]
      exact wgate_fix_input emb RG hRG.1 Ul harev l P
  have hmain : ∀ (L : List (Fin n)), L.Nodup → k.rev ∈ L → (L.map f).prod.mulVec v₀ = tgt := by
    intro L hnodup hmem
    induction L with
    | nil => simp at hmem
    | cons a as ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
      by_cases ha : a = k.rev
      · subst ha
        rw [hfix_in as hnodup.1]
        dsimp [f]
        rw [Fin.rev_rev]
        exact wgate_step_k emb hemb RG hRG.1 Ul hUl (τ k) l P
      · have hmem_as : k.rev ∈ as := (List.mem_cons.mp hmem).resolve_left (Ne.symm ha)
        rw [ih hnodup.2 hmem_as]
        have harev : τ a.rev ≠ τ k := fun heq => ha (by
          have : a.rev = k := τ.injective heq
          rw [← this, Fin.rev_rev])
        exact wgate_fix_target H T hT he BH Nminus RH hRH RG hRG hAd emb hemb Ul hUl harev l P
  have hgoal := hmain (List.finRange n) (List.nodup_finRange n) (List.mem_finRange k.rev)
  rw [← List.ofFn_eq_map] at hgoal
  exact hgoal
