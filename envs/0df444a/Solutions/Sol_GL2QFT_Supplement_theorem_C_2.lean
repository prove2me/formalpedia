-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_C_2
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:28:31.260928+00:00
-- url     : https://prove2.me/submissions/9d4085c3-451a-4d68-9b00-1ba7b8328db5

import Definitions.Def_GL2QFT_Supplement_MackeyMult

noncomputable section

open Classical
open scoped Matrix ComplexConjugate

namespace GL2QFT.Supplement.MackeyMultProof

open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.Mackey GL2QFT.Supplement.MackeyMult

/-! ### Section 1: Unitary matrices, Schur's lemma, Schur orthogonality, Peter–Weyl completeness -/

private lemma isUnitaryRep_mul_conjTranspose {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g * (R g)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hR.2 g)

private lemma isUnitaryRep_conjTranspose_mul {G ι : Type} [Monoid G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    (R g)ᴴ * R g = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hR.2 g)

private lemma isUnitaryRep_inv_eq_conjTranspose {G ι : Type} [Group G] [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hR : IsUnitaryRep R) (g : G) :
    R g⁻¹ = (R g)ᴴ := by
  have h1 : R g * R g⁻¹ = 1 := by
    rw [← hR.1.2, mul_inv_cancel, hR.1.1]
  have h2 : (R g)ᴴ * R g = 1 := isUnitaryRep_conjTranspose_mul hR g
  calc R g⁻¹ = 1 * R g⁻¹ := (Matrix.one_mul _).symm
    _ = ((R g)ᴴ * R g) * R g⁻¹ := by rw [h2]
    _ = (R g)ᴴ * (R g * R g⁻¹) := Matrix.mul_assoc _ _ _
    _ = (R g)ᴴ := by rw [h1, Matrix.mul_one]

private lemma mul_isUnitary {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq γ]
    {A : Matrix α β ℂ} {B : Matrix β γ ℂ}
    (hA1 : A * Aᴴ = 1) (hA2 : Aᴴ * A = 1) (hB1 : B * Bᴴ = 1) (hB2 : Bᴴ * B = 1) :
    (A * B) * (A * B)ᴴ = 1 ∧ (A * B)ᴴ * (A * B) = 1 := by
  constructor
  · calc (A * B) * (A * B)ᴴ
        = A * (B * Bᴴ) * Aᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = A * Aᴴ := by rw [hB1, Matrix.mul_one]
      _ = 1 := hA1
  · calc (A * B)ᴴ * (A * B)
        = Bᴴ * (Aᴴ * A) * B := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * B := by rw [hA2, Matrix.mul_one]
      _ = 1 := hB2

private lemma card_eq_of_isUnitary {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] {L : Matrix ι₁ ι₂ ℂ}
    (h1 : L * Lᴴ = 1) (h2 : Lᴴ * L = 1) :
    Fintype.card ι₁ = Fintype.card ι₂ := by
  have htr : (Fintype.card ι₁ : ℂ) = (Fintype.card ι₂ : ℂ) := by
    calc (Fintype.card ι₁ : ℂ)
        = (1 : Matrix ι₁ ι₁ ℂ).trace := by simp
      _ = (L * Lᴴ).trace := by rw [h1]
      _ = (Lᴴ * L).trace := Matrix.trace_mul_comm L Lᴴ
      _ = (1 : Matrix ι₂ ι₂ ℂ).trace := by rw [h2]
      _ = (Fintype.card ι₂ : ℂ) := by simp
  exact Nat.cast_injective htr

private def permMatrix {α β : Type} (e : α ≃ β) : Matrix α β ℂ :=
  Matrix.of fun a b => if e a = b then 1 else 0

private lemma permMatrix_isUnitary {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    permMatrix e * (permMatrix e)ᴴ = 1 ∧ (permMatrix e)ᴴ * permMatrix e = 1 := by
  constructor
  · ext a₁ a₂
    simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply]
    rw [Finset.sum_eq_single (e a₁)]
    · simp [e.injective.eq_iff, eq_comm]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb; exact False.elim (hb (Finset.mem_univ _))
  · ext b₁ b₂
    simp only [Matrix.mul_apply, permMatrix, Matrix.of_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply]
    rw [Finset.sum_eq_single (e.symm b₁)]
    · simp
    · intro a _ ha
      have hne : e a ≠ b₁ := fun h => ha (e.eq_symm_apply.mpr h)
      simp [hne]
    · intro ha; exact False.elim (ha (Finset.mem_univ _))

private lemma permMatrix_mul {α β γ : Type} [Fintype β] (e : α ≃ β) (M : Matrix β γ ℂ)
    (a : α) (c : γ) :
    (permMatrix e * M) a c = M (e a) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e a)]
  · simp [permMatrix]
  · intro b _ hb
    simp [permMatrix, Ne.symm hb]
  · intro hb; exact False.elim (hb (Finset.mem_univ _))

private def blockDiagMat {I : Type} {α β : I → Type}
    (M : ∀ i, Matrix (α i) (β i) ℂ) : Matrix (Σ i, α i) (Σ i, β i) ℂ :=
  Matrix.of fun x y =>
    if h : x.1 = y.1 then M y.1 (cast (congrArg α h) x.2) y.2 else 0

private lemma blockDiagMat_isUnitary {I : Type} [Fintype I] [DecidableEq I] {α β : I → Type}
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, DecidableEq (α i)] [∀ i, DecidableEq (β i)]
    (M : ∀ i, Matrix (α i) (β i) ℂ)
    (hM : ∀ i, M i * (M i)ᴴ = 1 ∧ (M i)ᴴ * M i = 1) :
    blockDiagMat M * (blockDiagMat M)ᴴ = 1 ∧ (blockDiagMat M)ᴴ * blockDiagMat M = 1 := by
  constructor
  · ext ⟨i, a⟩ ⟨i', a'⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single i]
    · by_cases hi : i' = i
      · subst hi
        have hrow : ∑ b : β i', blockDiagMat M ⟨i', a⟩ ⟨i', b⟩ * star (blockDiagMat M ⟨i', a'⟩ ⟨i', b⟩) =
            (M i' * (M i')ᴴ) a a' := by
          simp only [blockDiagMat, Matrix.of_apply, ↓reduceDIte, cast_eq, Matrix.mul_apply,
            Matrix.conjTranspose_apply]
        rw [hrow, (hM i').1, Matrix.one_apply]
        simp
      · have hzero : ∑ b : β i, blockDiagMat M ⟨i, a⟩ ⟨i, b⟩ * star (blockDiagMat M ⟨i', a'⟩ ⟨i, b⟩) =
            0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          simp [blockDiagMat, hi]
        rw [hzero]
        have hne : (⟨i, a⟩ : Σ k, α k) ≠ ⟨i', a'⟩ := fun h => hi (congrArg Sigma.fst h).symm
        simp [hne]
    · intro j _ hj
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [blockDiagMat, hj.symm]
    · intro hj; exact False.elim (hj (Finset.mem_univ _))
  · ext ⟨j, b⟩ ⟨j', b'⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single j]
    · by_cases hj : j' = j
      · subst hj
        have hcol : ∑ a : α j', star (blockDiagMat M ⟨j', a⟩ ⟨j', b⟩) * blockDiagMat M ⟨j', a⟩ ⟨j', b'⟩ =
            ((M j')ᴴ * M j') b b' := by
          simp only [blockDiagMat, Matrix.of_apply, ↓reduceDIte, cast_eq, Matrix.mul_apply,
            Matrix.conjTranspose_apply]
        rw [hcol, (hM j').2, Matrix.one_apply]
        simp
      · have hzero : ∑ a : α j, star (blockDiagMat M ⟨j, a⟩ ⟨j, b⟩) *
            blockDiagMat M ⟨j, a⟩ ⟨j', b'⟩ = 0 := by
          refine Finset.sum_eq_zero fun a _ => ?_
          simp [blockDiagMat, Ne.symm hj]
        rw [hzero]
        have hne : (⟨j, b⟩ : Σ k, β k) ≠ ⟨j', b'⟩ := fun h => hj (congrArg Sigma.fst h).symm
        simp [hne]
    · intro i _ hi
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [blockDiagMat, hi]
    · intro hi; exact False.elim (hi (Finset.mem_univ _))

private lemma blockDiagMat_mul {I : Type} [Fintype I] {α β : I → Type} {γ : Type}
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (M : ∀ i, Matrix (α i) (β i) ℂ) (A : Matrix (Σ i, β i) γ ℂ) (i : I) (a : α i) (z : γ) :
    (blockDiagMat M * A) ⟨i, a⟩ z = ∑ b : β i, M i a b * A ⟨i, b⟩ z := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [blockDiagMat]
  · intro j _ hj
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [blockDiagMat, hj.symm]
  · intro hj; exact False.elim (hj (Finset.mem_univ _))

private lemma ker_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₁ (LinearMap.ker A.mulVecLin) := by
  intro g v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hA g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

private lemma range_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₂ (LinearMap.range A.mulVecLin) := by
  intro g w hw
  rcases hw with ⟨v, rfl⟩
  refine ⟨R₁ g *ᵥ v, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA g]

private lemma mulVecLin_eq_zero_iff {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Matrix ι₂ ι₁ ℂ) : (∀ v, A *ᵥ v = 0) ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have := congr_fun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  · intro h v
    subst h
    simp

private lemma schur_zero_of_not_repEquiv {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
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

private lemma schur_eq_smul_one {G ι : Type} [Fintype ι] [DecidableEq ι]
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

private lemma schur_orthogonality_ne {K ι₁ ι₂ : Type} [Group K] [Fintype K]
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

private lemma schur_orthogonality_eq {K ι : Type} [Group K] [Fintype K]
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

private lemma fourierMatrix_mul_conjTranspose {K Λ : Type} [Group K] [Fintype K]
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
          (Fintype.card (B μ) : ℂ) / (Fintype.card K : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      rfl
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

private lemma fourierMatrix_conjTranspose_mul {K Λ : Type} [Group K] [Fintype K]
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
          have := Matrix.toLin_apply b b (ρ x) (b.equivFun.symm v)
          rw [Matrix.toLin_toMatrix] at this
          have hrep : ⇑(b.repr (b.equivFun.symm v)) = v := b.equivFun.apply_symm_apply v
          rw [hrep, ← b.equivFun_symm_apply] at this
          exact this
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
        rwa [b.equivFun.apply_symm_apply, map_zero] at hv0
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
        have : w = v := b.equivFun.symm.injective hvw
        subst this
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
          ∑ c : Fin n, (∑ j : B μ, (∑ i : B μ, P_mat c i * star (R μ g j i)) * Q_mat j a₀) *
            (b c : K → ℂ) 1 =
          ∑ i : B μ, ∑ j : B μ, (∑ c : Fin n, P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1) *
            star (R μ g j i) := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have h1 : ∀ j : B μ,
            ∑ c : Fin n, ∑ i : B μ, P_mat c i * star (R μ g j i) * Q_mat j a₀ * (b c : K → ℂ) 1 =
            ∑ i : B μ, ∑ c : Fin n, P_mat c i * Q_mat j a₀ * (b c : K → ℂ) 1 * star (R μ g j i) := by
          intro j
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by ring
        simp_rw [h1]
        exact Finset.sum_comm
      change ∑ c : Fin n, (∑ j : B μ, (∑ i : B μ, P_mat c i * star (R μ g j i)) * Q_mat j a₀) *
          (b c : K → ℂ) 1 = _
      rw [hswap]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      dsimp only [coeff]
      simp only [Complex.star_def]
      rw [mul_assoc]
      congr 1
      rw [← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]
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
          simp only [w, ip, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          have h3 : ∀ a, ∑ g : K, star (φ b g) * (ip (φ a) u * φ a g) =
              ip (φ a) u * ip (φ b) (φ a) := fun a => by
            simp only [ip, Finset.mul_sum]
            refine Finset.sum_congr rfl fun g _ => by ring
          rw [Finset.sum_congr rfl fun a _ => (h3 a).trans (by rw [hip_φ])]
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          rfl
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

/-! ### Section 2: General `UIndMultT` unitarity via Fourier factorization -/

private def UIndMultT {G' : Type} [Group G'] (T' : Set G') [Fintype T']
    {ΛH' ΛG' : Type} [Fintype ΛH'] (BH' : ΛH' → Type) [∀ l, Fintype (BH' l)]
    (mult' : ΛH' → ΛG' → ℕ)
    (RG' : ∀ μ, G' → Matrix (AdBasM BH' mult' μ) (AdBasM BH' mult' μ) ℂ) (l : ΛH') :
    Matrix (Σ μ : ΛG', AdBasM BH' mult' μ × Fin (mult' l μ)) (T' × BH' l) ℂ :=
  Matrix.of fun o tP =>
    (Real.sqrt ((Fintype.card (AdBasM BH' mult' o.1) : ℝ) /
      ((Fintype.card (BH' l) : ℝ) * (Fintype.card T' : ℝ))) : ℂ) *
      RG' o.1 (tP.1 : G') o.2.1 ⟨l, o.2.2, tP.2⟩

private abbrev RHSOutM {ΛH' ΛG' : Type} (BH' : ΛH' → Type) (mult' : ΛH' → ΛG' → ℕ) : Type :=
  Σ l : ΛH', (Σ μ : ΛG', AdBasM BH' mult' μ × Fin (mult' l μ)) × BH' l

private def UIndTensorIM {G' : Type} [Group G'] (T' : Set G') [Fintype T']
    {ΛH' ΛG' : Type} [Fintype ΛH'] (BH' : ΛH' → Type) [∀ l, Fintype (BH' l)]
    (mult' : ΛH' → ΛG' → ℕ)
    (RG' : ∀ μ, G' → Matrix (AdBasM BH' mult' μ) (AdBasM BH' mult' μ) ℂ) :
    Matrix (RHSOutM BH' mult') (T' × Σ l : ΛH', BH' l × BH' l) ℂ :=
  Matrix.of fun out inp =>
    if e : inp.2.1 = out.1 then
      UIndMultT T' BH' mult' RG' out.1 out.2.1 (inp.1, cast (congrArg BH' e) inp.2.2.1) *
        (if cast (congrArg BH' e) inp.2.2.2 = out.2.2 then 1 else 0)
    else 0

private def identMEquiv {ΛH' ΛG' : Type} (BH' : ΛH' → Type) (mult' : ΛH' → ΛG' → ℕ) :
    (Σ μ : ΛG', AdBasM BH' mult' μ × AdBasM BH' mult' μ) ≃ RHSOutM BH' mult' where
  toFun o := ⟨o.2.2.1, ⟨o.1, o.2.1, o.2.2.2.1⟩, o.2.2.2.2⟩
  invFun x := ⟨x.2.1.1, x.2.1.2.1, ⟨x.1, x.2.1.2.2, x.2.2⟩⟩
  left_inv o := by rcases o with ⟨μ, Q, ⟨l, b, R⟩⟩; rfl
  right_inv x := by rcases x with ⟨l, ⟨μ, Q, b⟩, R⟩; rfl

private lemma enc_mul_conjTranspose {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G)) :
    GL2QFT.Induction.Enc H T * (GL2QFT.Induction.Enc H T)ᴴ = 1 := by
  let e : T × H ≃ G := Equiv.ofBijective _ hT
  ext th₁ th₂
  simp only [Matrix.mul_apply, GL2QFT.Induction.Enc, Matrix.of_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply]
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

private lemma enc_conjTranspose_mul {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (H : Set G)) :
    (GL2QFT.Induction.Enc H T)ᴴ * GL2QFT.Induction.Enc H T = 1 := by
  let e : T × H ≃ G := Equiv.ofBijective _ hT
  ext g₁ g₂
  simp only [Matrix.mul_apply, GL2QFT.Induction.Enc, Matrix.of_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply]
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

private lemma fourier_factorization_mult {G' : Type} [Group G'] [Fintype G']
    (H' : Subgroup G') [Fintype H'] (T' : Set G') [Fintype T']
    (hT' : Subgroup.IsComplement T' (H' : Set G'))
    {ΛH' ΛG' : Type} [Fintype ΛH'] [Fintype ΛG'] (BH' : ΛH' → Type) [∀ l, Fintype (BH' l)]
    [∀ l, DecidableEq (BH' l)] (mult' : ΛH' → ΛG' → ℕ)
    (RH' : ∀ l, H' → Matrix (BH' l) (BH' l) ℂ)
    (RG' : ∀ μ, G' → Matrix (AdBasM BH' mult' μ) (AdBasM BH' mult' μ) ℂ)
    (hRG' : ∀ μ, IsMatRep (RG' μ)) (hAd' : IsAdaptedMult H' BH' mult' RH' RG') :
    fourierMatrix RG' =
      ((UIndTensorIM T' BH' mult' RG' * Matrix.kronecker (1 : Matrix T' T' ℂ) (fourierMatrix RH')) *
        GL2QFT.Induction.Enc H' T').submatrix (identMEquiv BH' mult') id := by
  let e : T' × H' ≃ G' := Equiv.ofBijective _ hT'
  have hcard : Fintype.card G' = Fintype.card T' * Fintype.card H' := by
    rw [← Fintype.card_prod, Fintype.card_congr e]
  ext ⟨μ, Q, ⟨l, b, R⟩⟩ g
  let th₀ := e.symm g
  let t := th₀.1
  let h := th₀.2
  have hth_eq : g = (t : G') * (h : G') := (e.apply_symm_apply g).symm
  simp only [Matrix.submatrix_apply, id_eq]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (t, h)]
  · simp only [GL2QFT.Induction.Enc, Matrix.of_apply, if_pos hth_eq, mul_one]
    have hsplit :
        (UIndTensorIM T' BH' mult' RG' * Matrix.kronecker (1 : Matrix T' T' ℂ) (fourierMatrix RH'))
            (identMEquiv BH' mult' ⟨μ, Q, ⟨l, b, R⟩⟩) (t, h) =
          ∑ P : BH' l,
            ((Real.sqrt ((Fintype.card (AdBasM BH' mult' μ) : ℝ) /
              ((Fintype.card (BH' l) : ℝ) * (Fintype.card T' : ℝ))) : ℂ) *
              RG' μ (t : G') Q ⟨l, b, P⟩) *
              ((Real.sqrt ((Fintype.card (BH' l) : ℝ) / (Fintype.card H' : ℝ)) : ℂ) * RH' l h P R) := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single t]
      · rw [Fintype.sum_sigma, Finset.sum_eq_single l]
        · rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun P _ => ?_
          rw [Finset.sum_eq_single R]
          · simp [UIndTensorIM, identMEquiv, UIndMultT, fourierMatrix]
          · intro R' _ hR'; simp [UIndTensorIM, identMEquiv, hR']
          · intro hR'; exact False.elim (hR' (Finset.mem_univ _))
        · intro l' _ hl'
          refine Finset.sum_eq_zero fun PR' _ => ?_
          simp [UIndTensorIM, identMEquiv, hl']
        · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
      · intro t' _ ht'
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [ht']
      · intro ht'; exact False.elim (ht' (Finset.mem_univ _))
    rw [hsplit]
    dsimp only [fourierMatrix]
    rw [Matrix.of_apply]
    have hsqrt :
        (Real.sqrt ((Fintype.card (AdBasM BH' mult' μ) : ℝ) /
          ((Fintype.card (BH' l) : ℝ) * (Fintype.card T' : ℝ))) : ℂ) *
        (Real.sqrt ((Fintype.card (BH' l) : ℝ) / (Fintype.card H' : ℝ)) : ℂ) =
        (Real.sqrt ((Fintype.card (AdBasM BH' mult' μ) : ℝ) / (Fintype.card G' : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
      congr 2
      rw [hcard]
      push_cast
      have hd_ne : (Fintype.card (BH' l) : ℝ) ≠ 0 := by
        have : Nonempty (BH' l) := ⟨R⟩
        exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp
    have had_sum :
        ∑ P : BH' l, RG' μ (t : G') Q ⟨l, b, P⟩ * RH' l h P R =
          ∑ S : AdBasM BH' mult' μ, RG' μ (t : G') Q S * RG' μ (h : G') S ⟨l, b, R⟩ := by
      symm
      rw [Fintype.sum_sigma, Finset.sum_eq_single l]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
        · refine Finset.sum_congr rfl fun P _ => ?_
          have := hAd' μ h ⟨l, b, P⟩ ⟨l, b, R⟩
          dsimp only at this
          rw [dif_pos rfl] at this
          dsimp only [cast_eq] at this
          rw [if_pos rfl] at this
          rw [this]
        · intro b' _ hb'
          refine Finset.sum_eq_zero fun P _ => ?_
          have := hAd' μ h ⟨l, b', P⟩ ⟨l, b, R⟩
          dsimp only at this
          rw [dif_pos rfl] at this
          dsimp only [cast_eq] at this
          rw [if_neg hb'] at this
          rw [this, mul_zero]
        · intro hb'; exact False.elim (hb' (Finset.mem_univ _))
      · intro l' _ hl'
        refine Finset.sum_eq_zero fun br _ => ?_
        have := hAd' μ h ⟨l', br⟩ ⟨l, b, R⟩
        dsimp only at this
        rw [dif_neg hl'] at this
        rw [this, mul_zero]
      · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
    calc (Real.sqrt ((Fintype.card (AdBasM BH' mult' μ) : ℝ) / (Fintype.card G' : ℝ)) : ℂ) *
          RG' μ g Q ⟨l, b, R⟩
        = (Real.sqrt ((Fintype.card (AdBasM BH' mult' μ) : ℝ) / (Fintype.card G' : ℝ)) : ℂ) *
            (∑ S : AdBasM BH' mult' μ, RG' μ (t : G') Q S * RG' μ (h : G') S ⟨l, b, R⟩) := by
            rw [hth_eq, (hRG' μ).2 (t : G') (h : G'), Matrix.mul_apply]
      _ = (Real.sqrt ((Fintype.card (AdBasM BH' mult' μ) : ℝ) / (Fintype.card G' : ℝ)) : ℂ) *
            ∑ P : BH' l, RG' μ (t : G') Q ⟨l, b, P⟩ * RH' l h P R := by rw [had_sum]
      _ = ∑ P : BH' l,
            ((Real.sqrt ((Fintype.card (AdBasM BH' mult' μ) : ℝ) /
              ((Fintype.card (BH' l) : ℝ) * (Fintype.card T' : ℝ))) : ℂ) *
              RG' μ (t : G') Q ⟨l, b, P⟩) *
              ((Real.sqrt ((Fintype.card (BH' l) : ℝ) / (Fintype.card H' : ℝ)) : ℂ) * RH' l h P R) := by
            rw [← hsqrt, Finset.mul_sum]
            refine Finset.sum_congr rfl fun P _ => by ring
  · intro th _ hth
    have hne : g ≠ (th.1 : G') * (th.2 : G') := fun heq =>
      hth (e.injective (hth_eq.symm.trans heq).symm)
    simp only [GL2QFT.Induction.Enc, Matrix.of_apply, if_neg hne, mul_zero]
  · intro hth; exact False.elim (hth (Finset.mem_univ _))

private lemma kronecker_conjTranspose {l m n p : Type}
    (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
    (Matrix.kronecker A B)ᴴ = Matrix.kronecker Aᴴ Bᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.conjTranspose_apply]

private lemma uindTensorIM_isUnitary {G' : Type} [Group G'] [Fintype G']
    (H' : Subgroup G') [Fintype H'] (T' : Set G') [Fintype T']
    (hT' : Subgroup.IsComplement T' (H' : Set G'))
    {ΛH' ΛG' : Type} [Fintype ΛH'] [Fintype ΛG'] (BH' : ΛH' → Type) [∀ l, Fintype (BH' l)]
    [∀ l, DecidableEq (BH' l)] (mult' : ΛH' → ΛG' → ℕ)
    (RH' : ∀ l, H' → Matrix (BH' l) (BH' l) ℂ) (hRH' : IsIrrepSystem RH')
    (RG' : ∀ μ, G' → Matrix (AdBasM BH' mult' μ) (AdBasM BH' mult' μ) ℂ) (hRG' : IsIrrepSystem RG')
    (hAd' : IsAdaptedMult H' BH' mult' RH' RG') :
    UIndTensorIM T' BH' mult' RG' * (UIndTensorIM T' BH' mult' RG')ᴴ = 1 ∧
      (UIndTensorIM T' BH' mult' RG')ᴴ * UIndTensorIM T' BH' mult' RG' = 1 := by
  let eId := identMEquiv BH' mult'
  let FG' : Matrix (RHSOutM BH' mult') G' ℂ := (fourierMatrix RG').submatrix eId.symm id
  have hFG'_mul : FG' * FG'ᴴ = 1 := by
    have hFG := fourierMatrix_mul_conjTranspose hRG'
    ext r₁ r₂
    simpa [FG', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      eId.symm.injective.eq_iff] using
      congr_fun (congr_fun hFG (eId.symm r₁)) (eId.symm r₂)
  have hFG'_conj : FG'ᴴ * FG' = 1 := by
    have hFG := fourierMatrix_conjTranspose_mul hRG'
    ext g₁ g₂
    simp only [FG', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq]
    rw [Fintype.sum_equiv eId.symm _ (fun r => star (fourierMatrix RG' r g₁) * fourierMatrix RG' r g₂)
      fun _ => rfl]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congr_fun (congr_fun hFG g₁) g₂
  let K := Matrix.kronecker (1 : Matrix T' T' ℂ) (fourierMatrix RH')
  have hK_mul : K * Kᴴ = 1 := by
    have hF := fourierMatrix_mul_conjTranspose hRH'
    ext ⟨t₁, x₁⟩ ⟨t₂, x₂⟩
    simp only [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single t₁]
    · by_cases ht : t₂ = t₁
      · subst ht
        have hF' := congr_fun (congr_fun hF x₁) x₂
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hF'
        simpa [Complex.star_def] using hF'
      · simp [ht, Ne.symm ht]
    · intro t _ ht
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [ht.symm]
    · intro ht; exact False.elim (ht (Finset.mem_univ _))
  have hK_conj : Kᴴ * K = 1 := by
    have hF := fourierMatrix_conjTranspose_mul hRH'
    ext ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    simp only [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single t₁]
    · by_cases ht : t₂ = t₁
      · subst ht
        have hF' := congr_fun (congr_fun hF h₁) h₂
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hF'
        have hlhs :
            ∑ y : Σ l, BH' l × BH' l,
              star (Matrix.kronecker (1 : Matrix T' T' ℂ) (fourierMatrix RH') (t₂, y) (t₂, h₁)) *
                Matrix.kronecker (1 : Matrix T' T' ℂ) (fourierMatrix RH') (t₂, y) (t₂, h₂) =
            ∑ y : Σ l, BH' l × BH' l,
              star (fourierMatrix RH' y h₁) * fourierMatrix RH' y h₂ := by
          refine Finset.sum_congr rfl fun y _ => ?_
          simp
        rw [hlhs, hF']
        split_ifs <;> simp_all
      · simp [Ne.symm ht]
    · intro t _ ht
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [ht]
    · intro ht; exact False.elim (ht (Finset.mem_univ _))
  let M := K * GL2QFT.Induction.Enc H' T'
  have hM_unit := mul_isUnitary hK_mul (by convert hK_conj)
    (by convert enc_mul_conjTranspose H' T' hT') (enc_conjTranspose_mul H' T' hT')
  have hfact := fourier_factorization_mult H' T' hT' BH' mult' RH' RG' (fun μ => (hRG'.1 μ).1) hAd'
  have hFG'_eq : FG' = UIndTensorIM T' BH' mult' RG' * M := by
    ext r g
    have := congr_fun (congr_fun hfact (eId.symm r)) g
    simpa [FG', M, K, eId, identMEquiv, Matrix.mul_assoc] using this
  have hU_eq : UIndTensorIM T' BH' mult' RG' = FG' * Mᴴ := by
    calc UIndTensorIM T' BH' mult' RG'
        = UIndTensorIM T' BH' mult' RG' * (M * Mᴴ) := by rw [hM_unit.1, Matrix.mul_one]
      _ = (UIndTensorIM T' BH' mult' RG' * M) * Mᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = FG' * Mᴴ := by rw [← hFG'_eq]
  rw [hU_eq]
  exact mul_isUnitary hFG'_mul hFG'_conj
    (by dsimp only [M]; rw [Matrix.conjTranspose_conjTranspose]; convert hM_unit.2)
    (by dsimp only [M]; rw [Matrix.conjTranspose_conjTranspose]; convert hM_unit.1)

private lemma uindMultT_isUnitary {G' : Type} [Group G'] [Fintype G']
    (H' : Subgroup G') [Fintype H'] (T' : Set G') [Fintype T']
    (hT' : Subgroup.IsComplement T' (H' : Set G'))
    {ΛH' ΛG' : Type} [Fintype ΛH'] [Fintype ΛG'] (BH' : ΛH' → Type) [∀ l, Fintype (BH' l)]
    [∀ l, DecidableEq (BH' l)] (mult' : ΛH' → ΛG' → ℕ)
    (RH' : ∀ l, H' → Matrix (BH' l) (BH' l) ℂ) (hRH' : IsIrrepSystem RH')
    (RG' : ∀ μ, G' → Matrix (AdBasM BH' mult' μ) (AdBasM BH' mult' μ) ℂ) (hRG' : IsIrrepSystem RG')
    (hAd' : IsAdaptedMult H' BH' mult' RH' RG') (l : ΛH') :
    UIndMultT T' BH' mult' RG' l * (UIndMultT T' BH' mult' RG' l)ᴴ = 1 ∧
      (UIndMultT T' BH' mult' RG' l)ᴴ * UIndMultT T' BH' mult' RG' l = 1 := by
  obtain ⟨R₀⟩ := (hRH'.2.1 l).1
  obtain ⟨hU1, hU2⟩ := uindTensorIM_isUnitary H' T' hT' BH' mult' RH' hRH' RG' hRG' hAd'
  constructor
  · ext M₁ M₂
    have hentry := congr_fun (congr_fun hU1 ⟨l, M₁, R₀⟩) ⟨l, M₂, R₀⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry ⊢
    have hred :
        ∑ inp : T' × Σ l' : ΛH', BH' l' × BH' l',
          UIndTensorIM T' BH' mult' RG' ⟨l, M₁, R₀⟩ inp *
            star (UIndTensorIM T' BH' mult' RG' ⟨l, M₂, R₀⟩ inp) =
        ∑ tP : T' × BH' l,
          UIndMultT T' BH' mult' RG' l M₁ tP * star (UIndMultT T' BH' mult' RG' l M₂ tP) := by
      rw [Fintype.sum_prod_type]
      have hcomm :
          ∑ t : T', ∑ x : Σ l' : ΛH', BH' l' × BH' l',
            UIndTensorIM T' BH' mult' RG' ⟨l, M₁, R₀⟩ (t, x) *
              star (UIndTensorIM T' BH' mult' RG' ⟨l, M₂, R₀⟩ (t, x)) =
          ∑ t : T', ∑ P : BH' l,
            UIndMultT T' BH' mult' RG' l M₁ (t, P) * star (UIndMultT T' BH' mult' RG' l M₂ (t, P)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Fintype.sum_sigma, Finset.sum_eq_single l]
        · rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun P _ => ?_
          rw [Finset.sum_eq_single R₀]
          · simp [UIndTensorIM]
          · intro R' _ hR'; simp [UIndTensorIM, hR']
          · intro hR'; exact False.elim (hR' (Finset.mem_univ _))
        · intro l' _ hl'
          refine Finset.sum_eq_zero fun x _ => ?_
          simp [UIndTensorIM, hl']
        · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
      rw [hcomm]
      exact (Fintype.sum_prod_type (f := fun tP : T' × BH' l =>
        UIndMultT T' BH' mult' RG' l M₁ tP * star (UIndMultT T' BH' mult' RG' l M₂ tP))).symm
    rw [← hred, hentry]
    have heq : (⟨l, M₁, R₀⟩ : RHSOutM BH' mult') = ⟨l, M₂, R₀⟩ ↔ M₁ = M₂ := by simp
    simp [heq]
  · ext ⟨t₁, P₁⟩ ⟨t₂, P₂⟩
    have hentry := congr_fun (congr_fun hU2 (t₁, ⟨l, P₁, R₀⟩)) (t₂, ⟨l, P₂, R₀⟩)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry ⊢
    have hred :
        ∑ out : RHSOutM BH' mult',
          star (UIndTensorIM T' BH' mult' RG' out (t₁, ⟨l, P₁, R₀⟩)) *
            UIndTensorIM T' BH' mult' RG' out (t₂, ⟨l, P₂, R₀⟩) =
        ∑ M : Σ μ : ΛG', AdBasM BH' mult' μ × Fin (mult' l μ),
          star (UIndMultT T' BH' mult' RG' l M (t₁, P₁)) *
            UIndMultT T' BH' mult' RG' l M (t₂, P₂) := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single l]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [Finset.sum_eq_single R₀]
        · simp [UIndTensorIM]
        · intro R' _ hR'; simp [UIndTensorIM, hR'.symm]
        · intro hR'; exact False.elim (hR' (Finset.mem_univ _))
      · intro l' _ hl'
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [UIndTensorIM, Ne.symm hl']
      · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
    rw [← hred, hentry]
    have heq : (t₁, (⟨l, (P₁, R₀)⟩ : Σ l : ΛH', BH' l × BH' l)) =
        (t₂, ⟨l, (P₂, R₀)⟩) ↔ (t₁, P₁) = (t₂, P₂) := by simp
    simp [heq]

/-! ### Section 3: Mackey transversal `mackeyT` and `UIndMult` unitarity -/

private lemma mackeyT_isComplement {G : Type} [Group G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H)) :
    Subgroup.IsComplement (mackeyT H Ω Tω) (H : Set G) := by
  constructor
  · rintro ⟨t₁, h₁⟩ ⟨t₂, h₂⟩ heq
    dsimp only at heq
    obtain ⟨ω₁, hω₁, a₁, ha₁, ht₁⟩ := t₁.2
    obtain ⟨ω₂, hω₂, a₂, ha₂, ht₂⟩ := t₂.2
    have heq' : ((a₁ : G) * ω₁) * (h₁ : G) = ((a₂ : G) * ω₂) * (h₂ : G) := by
      simpa [ht₁, ht₂] using heq
    have hω_eq : (⟨ω₁, hω₁⟩ : Ω) = ⟨ω₂, hω₂⟩ := by
      have hEx := hΩ ((a₁ : G) * ω₁ * (h₁ : G))
      have u1 : ∃ h ∈ H, ∃ k ∈ H, (a₁ : G) * ω₁ * (h₁ : G) = h * ω₁ * k :=
        ⟨(a₁ : G), a₁.2, (h₁ : G), h₁.2, rfl⟩
      have u2 : ∃ h ∈ H, ∃ k ∈ H, (a₁ : G) * ω₁ * (h₁ : G) = h * ω₂ * k :=
        ⟨(a₂ : G), a₂.2, (h₂ : G), h₂.2, heq'⟩
      exact hEx.unique u1 u2
    have hω12 : ω₁ = ω₂ := congrArg Subtype.val hω_eq
    subst hω12
    have hconj : a₂⁻¹ * a₁ ∈ interSub H ω₁ := by
      change (a₂⁻¹ * a₁ : H) ∈ (H.map (MulAut.conj ω₁).toMonoidHom).subgroupOf H
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      refine ⟨(h₂ : G) * (h₁ : G)⁻¹, H.mul_mem h₂.2 (H.inv_mem h₁.2), ?_⟩
      change ω₁ * ((h₂ : G) * (h₁ : G)⁻¹) * ω₁⁻¹ = (a₂ : G)⁻¹ * (a₁ : G)
      have hmul : (a₁ : G) * ω₁ = (a₂ : G) * ω₁ * (h₂ : G) * (h₁ : G)⁻¹ := by
        calc (a₁ : G) * ω₁ = ((a₁ : G) * ω₁ * (h₁ : G)) * (h₁ : G)⁻¹ := by simp [mul_assoc]
          _ = ((a₂ : G) * ω₁ * (h₂ : G)) * (h₁ : G)⁻¹ := by rw [heq']
          _ = (a₂ : G) * ω₁ * (h₂ : G) * (h₁ : G)⁻¹ := by simp [mul_assoc]
      calc ω₁ * ((h₂ : G) * (h₁ : G)⁻¹) * ω₁⁻¹
          = (a₂ : G)⁻¹ * ((a₂ : G) * ω₁ * (h₂ : G) * (h₁ : G)⁻¹) * ω₁⁻¹ := by simp [mul_assoc]
        _ = (a₂ : G)⁻¹ * ((a₁ : G) * ω₁) * ω₁⁻¹ := by rw [← hmul]
        _ = (a₂ : G)⁻¹ * (a₁ : G) := by simp [mul_assoc]
    have ha_eq : ((⟨a₁, ha₁⟩ : Tω ω₁), (⟨1, (interSub H ω₁).one_mem⟩ : (interSub H ω₁ : Set H))) =
        ((⟨a₂, ha₂⟩ : Tω ω₁), (⟨a₂⁻¹ * a₁, hconj⟩ : (interSub H ω₁ : Set H))) :=
      (hTω ω₁ hω₁).injective (by
        change (a₁ : H) * 1 = a₂ * (a₂⁻¹ * a₁)
        simp)
    have ha12 : a₁ = a₂ := congrArg (fun p => (p.1 : H)) ha_eq
    have ht12 : t₁ = t₂ := Subtype.ext (by rw [ht₁, ht₂, ha12])
    have hh12 : h₁ = h₂ := by
      apply Subtype.ext
      have : (t₁ : G) * (h₁ : G) = (t₁ : G) * (h₂ : G) := by
        calc (t₁ : G) * (h₁ : G) = (t₂ : G) * (h₂ : G) := heq
          _ = (t₁ : G) * (h₂ : G) := by rw [ht12]
      exact mul_left_cancel this
    exact Prod.ext ht12 hh12
  · intro g
    obtain ⟨⟨ω, hω⟩, ⟨h, hh, k, hk, hg⟩, _⟩ := hΩ g
    obtain ⟨⟨a, l⟩, hal⟩ := (hTω ω hω).surjective ⟨h, hh⟩
    have ha_eq : (a : H) * (l : H) = ⟨h, hh⟩ := hal
    have hl_mem : ω⁻¹ * ((l : H) : G) * ω ∈ H := interSub_conj_mem H ω l
    refine ⟨(⟨((a : H) : G) * ω, ⟨ω, hω, a, a.2, rfl⟩⟩,
      ⟨ω⁻¹ * ((l : H) : G) * ω * k, H.mul_mem hl_mem hk⟩), ?_⟩
    dsimp only
    calc (((a : H) : G) * ω) * (ω⁻¹ * ((l : H) : G) * ω * k)
        = ((a : H) : G) * ((l : H) : G) * ω * k := by simp [mul_assoc]
      _ = h * ω * k := by
          have : ((a : H) : G) * ((l : H) : G) = h := congrArg Subtype.val ha_eq
          rw [this]
      _ = g := hg.symm

private lemma complement_card_eq_index {K : Type} [Group K] [Fintype K]
    (L : Subgroup K) (T : Set K) [Fintype T] (hT : Subgroup.IsComplement T (L : Set K)) :
    Fintype.card T = L.index := by
  have h1 : Fintype.card T * Fintype.card L = Fintype.card K := by
    have hc := hT.card_mul_card
    simpa [Nat.card_eq_fintype_card] using hc
  have h2 : L.index * Fintype.card L = Fintype.card K := by
    have hc := L.index_mul_card
    simpa [Nat.card_eq_fintype_card] using hc
  have hL_pos : 0 < Fintype.card L := Fintype.card_pos
  exact Nat.eq_of_mul_eq_mul_right hL_pos (h1.trans h2.symm)

private lemma mackeyT_decomp {G : Type} [Group G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (t : mackeyT H Ω Tω) :
    ∃! p : (Σ ω : Ω, Tω ω.1), (((p.2 : H) : G) * (p.1 : G)) = (t : G) := by
  obtain ⟨ω, hω, a, ha, ht⟩ := t.2
  refine ⟨⟨⟨ω, hω⟩, ⟨a, ha⟩⟩, ht.symm, ?_⟩
  rintro ⟨⟨ω', hω'⟩, ⟨a', ha'⟩⟩ hp
  have hω_eq : (⟨ω', hω'⟩ : Ω) = ⟨ω, hω⟩ := by
    have hEx := hΩ (t : G)
    exact hEx.unique
      ⟨(a' : G), a'.2, 1, H.one_mem, by simpa [mul_assoc] using hp.symm⟩
      ⟨(a : G), a.2, 1, H.one_mem, by simpa [mul_assoc] using ht⟩
  obtain rfl : ω' = ω := congrArg Subtype.val hω_eq
  have ha_eq : ((a' : H) : G) = ((a : H) : G) := mul_right_cancel (hp.trans ht)
  have ha_sub : a' = a := Subtype.ext ha_eq
  congr 1
  exact Subtype.ext ha_sub

private lemma uindMult_isUnitary {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (mult : ΛH → ΛG → ℕ)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBasM BH mult μ) (AdBasM BH mult μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsAdaptedMult H BH mult RH RG) (l : ΛH) :
    UIndMult H Ω Tω BH mult RG l * (UIndMult H Ω Tω BH mult RG l)ᴴ = 1 ∧
      (UIndMult H Ω Tω BH mult RG l)ᴴ * UIndMult H Ω Tω BH mult RG l = 1 := by
  have hT := mackeyT_isComplement H Ω hΩ Tω hTω
  have hcard : Fintype.card (mackeyT H Ω Tω) = H.index :=
    complement_card_eq_index H (mackeyT H Ω Tω) hT
  have heq : UIndMult H Ω Tω BH mult RG l = UIndMultT (mackeyT H Ω Tω) BH mult RG l := by
    ext o tP
    simp [UIndMult, UIndMultT, hcard]
  rw [heq]
  exact uindMultT_isUnitary H (mackeyT H Ω Tω) hT BH mult RH hRH RG hRG hAd l

/-! ### Section 4: `NopM` two-sided unitarity -/

private def RHadM {G : Type} [Group G] {H : Subgroup G} {ΛH : Type} (BH : ΛH → Type)
    [∀ l, Fintype (BH l)]
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] (mL : ∀ ω, ΛH → Λω ω → ℕ)
    (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (ω : G) (ν : ΛH) (h : H) :
    Matrix (AdBasM (Bω ω) (fun κ ν => mL ω ν κ) ν)
      (AdBasM (Bω ω) (fun κ ν => mL ω ν κ) ν) ℂ :=
  (Lmat ω ν)ᴴ * RH ν h * Lmat ω ν

private lemma rHadM_isIrrepSystem {G : Type} [Group G] (H : Subgroup G) (Ω : Set G)
    {ΛH : Type} [Fintype ΛH] (BH : ΛH → Type) [∀ l, Fintype (BH l)] [∀ l, DecidableEq (BH l)]
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (mL : ∀ ω, ΛH → Λω ω → ℕ)
    (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
    (hL : ∀ ω ∈ Ω, ∀ ν, IsEmbeddingFamily H Bω (fun h => RH ν (h : H)) (mL ω ν) (Rω ω)
      (Lmat ω ν))
    (ω : G) (hω : ω ∈ Ω) :
    IsIrrepSystem (RHadM BH Bω mL Lmat RH ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ν
    have hL1 : Lmat ω ν * (Lmat ω ν)ᴴ = 1 := by convert (hL ω hω ν).1
    have hL2 : (Lmat ω ν)ᴴ * Lmat ω ν = 1 := by convert (hL ω hω ν).2.1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [RHadM, (hRH.1 ν).1.1, hL2]
    · intro h₁ h₂
      calc RHadM BH Bω mL Lmat RH ω ν (h₁ * h₂)
          = (Lmat ω ν)ᴴ * (RH ν h₁ * RH ν h₂) * Lmat ω ν := by
              simp [RHadM, (hRH.1 ν).1.2]
        _ = (Lmat ω ν)ᴴ * RH ν h₁ * (Lmat ω ν * (Lmat ω ν)ᴴ) * RH ν h₂ * Lmat ω ν := by
              rw [hL1, Matrix.mul_one]
              simp only [Matrix.mul_assoc]
        _ = RHadM BH Bω mL Lmat RH ω ν h₁ * RHadM BH Bω mL Lmat RH ω ν h₂ := by
              simp only [RHadM, Matrix.mul_assoc]
    · intro h
      rw [Matrix.mem_unitaryGroup_iff]
      change RHadM BH Bω mL Lmat RH ω ν h * (RHadM BH Bω mL Lmat RH ω ν h)ᴴ = 1
      calc RHadM BH Bω mL Lmat RH ω ν h * (RHadM BH Bω mL Lmat RH ω ν h)ᴴ
          = (Lmat ω ν)ᴴ * RH ν h * (Lmat ω ν * (Lmat ω ν)ᴴ) * (RH ν h)ᴴ * Lmat ω ν := by
              simp [RHadM, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (Lmat ω ν)ᴴ * (RH ν h * (RH ν h)ᴴ) * Lmat ω ν := by
              rw [hL1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = (Lmat ω ν)ᴴ * Lmat ω ν := by
              rw [isUnitaryRep_mul_conjTranspose (hRH.1 ν) h, Matrix.mul_one]
        _ = 1 := hL2
  · intro ν
    have hL1 : Lmat ω ν * (Lmat ω ν)ᴴ = 1 := by convert (hL ω hω ν).1
    have hL2 : (Lmat ω ν)ᴴ * Lmat ω ν = 1 := by convert (hL ω hω ν).2.1
    constructor
    · by_contra hemp
      have := not_nonempty_iff.mp hemp
      obtain ⟨q₀⟩ := (hRH.2.1 ν).1
      have h1 := congr_fun (congr_fun hL1 q₀) q₀
      simp only [Matrix.mul_apply, Fintype.sum_empty, Matrix.one_apply_eq] at h1
      norm_num at h1
    · intro W hW
      let L := Lmat ω ν
      let W' : Submodule ℂ (BH ν → ℂ) := W.map L.mulVecLin
      have hW' : IsInvariantSubspace (RH ν) W' := by
        intro h w hw
        rcases hw with ⟨v, hv, rfl⟩
        refine ⟨RHadM BH Bω mL Lmat RH ω ν h *ᵥ v, hW h v hv, ?_⟩
        simp only [Matrix.mulVecLin_apply, RHadM, Matrix.mulVec_mulVec]
        have hmat : L * (Lᴴ * RH ν h * L) = RH ν h * L := by
          calc L * (Lᴴ * RH ν h * L)
              = (L * Lᴴ) * (RH ν h * L) := by simp only [Matrix.mul_assoc]
            _ = RH ν h * L := by rw [show L * Lᴴ = 1 from hL1, Matrix.one_mul]
        rw [hmat]
      rcases (hRH.2.1 ν).2 W' hW' with hbot | htop
      · left
        rw [Submodule.eq_bot_iff]
        intro v hv
        have hLv : L *ᵥ v = 0 := by
          have : L.mulVecLin v ∈ W' := ⟨v, hv, rfl⟩
          rw [hbot] at this
          exact this
        calc v = (1 : Matrix _ _ ℂ) *ᵥ v := (Matrix.one_mulVec v).symm
          _ = (Lᴴ * L) *ᵥ v := by rw [show Lᴴ * L = 1 from hL2]
          _ = Lᴴ *ᵥ (L *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
          _ = 0 := by rw [hLv, Matrix.mulVec_zero]
      · right
        rw [eq_top_iff]
        intro v _
        have hmem : L.mulVecLin v ∈ W' := htop.symm ▸ Submodule.mem_top
        rcases hmem with ⟨u, hu, huv⟩
        have heq : u = v := by
          calc u = (Lᴴ * L) *ᵥ u := by rw [show Lᴴ * L = 1 from hL2, Matrix.one_mulVec]
            _ = Lᴴ *ᵥ (L *ᵥ u) := (Matrix.mulVec_mulVec _ _ _).symm
            _ = Lᴴ *ᵥ (L *ᵥ v) := by rw [show L *ᵥ u = L *ᵥ v from huv]
            _ = (Lᴴ * L) *ᵥ v := Matrix.mulVec_mulVec _ _ _
            _ = v := by rw [show Lᴴ * L = 1 from hL2, Matrix.one_mulVec]
        exact heq ▸ hu
  · intro ν ν' hne ⟨A, B, hAB, hBA, hInt⟩
    have hL1ν : Lmat ω ν * (Lmat ω ν)ᴴ = 1 := by convert (hL ω hω ν).1
    have hL2ν : (Lmat ω ν)ᴴ * Lmat ω ν = 1 := by convert (hL ω hω ν).2.1
    have hL1ν' : Lmat ω ν' * (Lmat ω ν')ᴴ = 1 := by convert (hL ω hω ν').1
    have hL2ν' : (Lmat ω ν')ᴴ * Lmat ω ν' = 1 := by convert (hL ω hω ν').2.1
    apply hRH.2.2.1 ν ν' hne
    refine ⟨Lmat ω ν' * A * (Lmat ω ν)ᴴ, Lmat ω ν * B * (Lmat ω ν')ᴴ, ?_, ?_, ?_⟩
    · calc (Lmat ω ν' * A * (Lmat ω ν)ᴴ) * (Lmat ω ν * B * (Lmat ω ν')ᴴ)
          = Lmat ω ν' * A * ((Lmat ω ν)ᴴ * Lmat ω ν) * B * (Lmat ω ν')ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = Lmat ω ν' * (A * B) * (Lmat ω ν')ᴴ := by
              rw [hL2ν, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hAB, Matrix.mul_one, hL1ν']
    · calc (Lmat ω ν * B * (Lmat ω ν')ᴴ) * (Lmat ω ν' * A * (Lmat ω ν)ᴴ)
          = Lmat ω ν * B * ((Lmat ω ν')ᴴ * Lmat ω ν') * A * (Lmat ω ν)ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = Lmat ω ν * (B * A) * (Lmat ω ν)ᴴ := by
              rw [hL2ν', Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hBA, Matrix.mul_one, hL1ν]
    · intro h _
      have hi := hInt h (Set.mem_univ _)
      calc (Lmat ω ν' * A * (Lmat ω ν)ᴴ) * RH ν h
          = Lmat ω ν' * A * (Lmat ω ν)ᴴ * RH ν h * (Lmat ω ν * (Lmat ω ν)ᴴ) := by
              rw [hL1ν, Matrix.mul_one]
        _ = Lmat ω ν' * (A * RHadM BH Bω mL Lmat RH ω ν h) * (Lmat ω ν)ᴴ := by
              simp only [RHadM, Matrix.mul_assoc]
        _ = Lmat ω ν' * (RHadM BH Bω mL Lmat RH ω ν' h * A) * (Lmat ω ν)ᴴ := by
              rw [hi]
        _ = (Lmat ω ν' * (Lmat ω ν')ᴴ) * RH ν' h * (Lmat ω ν' * A * (Lmat ω ν)ᴴ) := by
              simp only [RHadM, Matrix.mul_assoc]
        _ = RH ν' h * (Lmat ω ν' * A * (Lmat ω ν)ᴴ) := by
              rw [hL1ν', Matrix.one_mul]
  · intro ι _ _ ρ hρ1 hρ2
    obtain ⟨ν, A, B, hAB, hBA, hInt⟩ := hRH.2.2.2 ι ρ hρ1 hρ2
    have hL1 : Lmat ω ν * (Lmat ω ν)ᴴ = 1 := by convert (hL ω hω ν).1
    have hL2 : (Lmat ω ν)ᴴ * Lmat ω ν = 1 := by convert (hL ω hω ν).2.1
    refine ⟨ν, A * Lmat ω ν, (Lmat ω ν)ᴴ * B, ?_, ?_, ?_⟩
    · calc (A * Lmat ω ν) * ((Lmat ω ν)ᴴ * B)
          = A * (Lmat ω ν * (Lmat ω ν)ᴴ) * B := by simp only [Matrix.mul_assoc]
        _ = A * B := by rw [hL1, Matrix.mul_one]
        _ = 1 := hAB
    · calc ((Lmat ω ν)ᴴ * B) * (A * Lmat ω ν)
          = (Lmat ω ν)ᴴ * (B * A) * Lmat ω ν := by simp only [Matrix.mul_assoc]
        _ = (Lmat ω ν)ᴴ * Lmat ω ν := by rw [hBA, Matrix.mul_one]
        _ = 1 := hL2
    · intro h _
      calc (A * Lmat ω ν) * RHadM BH Bω mL Lmat RH ω ν h
          = A * (Lmat ω ν * (Lmat ω ν)ᴴ) * RH ν h * Lmat ω ν := by
              simp only [RHadM, Matrix.mul_assoc]
        _ = (A * RH ν h) * Lmat ω ν := by rw [hL1, Matrix.mul_one]
        _ = (ρ h * A) * Lmat ω ν := by rw [hInt h (Set.mem_univ _)]
        _ = ρ h * (A * Lmat ω ν) := Matrix.mul_assoc _ _ _

private lemma rHadM_isAdaptedMult {G : Type} [Group G] (H : Subgroup G) (Ω : Set G)
    {ΛH : Type} (BH : ΛH → Type) [∀ l, Fintype (BH l)] [∀ l, DecidableEq (BH l)]
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (mL : ∀ ω, ΛH → Λω ω → ℕ)
    (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
    (hL : ∀ ω ∈ Ω, ∀ ν, IsEmbeddingFamily H Bω (fun h => RH ν (h : H)) (mL ω ν) (Rω ω)
      (Lmat ω ν))
    (ω : G) (hω : ω ∈ Ω) :
    IsAdaptedMult (interSub H ω) (Bω ω) (fun κ ν => mL ω ν κ) (Rω ω)
      (RHadM BH Bω mL Lmat RH ω) := by
  intro ν h Q P
  have hL2 : (Lmat ω ν)ᴴ * Lmat ω ν = 1 := by convert (hL ω hω ν).2.1
  have hLint := (hL ω hω ν).2.2 h
  have heq : RHadM BH Bω mL Lmat RH ω ν (h : H) = blockRep H Bω (mL ω ν) (Rω ω) h := by
    calc RHadM BH Bω mL Lmat RH ω ν (h : H)
        = (Lmat ω ν)ᴴ * (RH ν (h : H) * Lmat ω ν) := by simp [RHadM, Matrix.mul_assoc]
      _ = (Lmat ω ν)ᴴ * (Lmat ω ν * blockRep H Bω (mL ω ν) (Rω ω) h) := by rw [← hLint]
      _ = ((Lmat ω ν)ᴴ * Lmat ω ν) * blockRep H Bω (mL ω ν) (Rω ω) h :=
            (Matrix.mul_assoc _ _ _).symm
      _ = blockRep H Bω (mL ω ν) (Rω ω) h := by rw [hL2, Matrix.one_mul]
  rw [heq]
  rfl

private lemma nopM_isUnitary {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH : Type} [Fintype ΛH] (BH : ΛH → Type) [∀ l, Fintype (BH l)] [∀ l, DecidableEq (BH l)]
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (mL : ∀ ω, ΛH → Λω ω → ℕ)
    (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
    (hL : ∀ ω ∈ Ω, ∀ ν, IsEmbeddingFamily H Bω (fun h => RH ν (h : H)) (mL ω ν) (Rω ω)
      (Lmat ω ν))
    (mE : ∀ ω, ΛH → Λω ω → ℕ)
    (Emat : ∀ ω l, Matrix (BH l) (Σ κ : Λω ω, Fin (mE ω l κ) × Bω ω κ) ℂ)
    (hE : ∀ ω ∈ Ω, ∀ l, IsEmbeddingFamily H Bω (twistRep H ω (RH l)) (mE ω l) (Rω ω) (Emat ω l))
    (l : ΛH) :
    NopM H Ω Tω BH Bω RH mL Lmat mE Emat l *
        (NopM H Ω Tω BH Bω RH mL Lmat mE Emat l)ᴴ = 1 ∧
      (NopM H Ω Tω BH Bω RH mL Lmat mE Emat l)ᴴ *
        NopM H Ω Tω BH Bω RH mL Lmat mE Emat l = 1 := by
  let T0 := mackeyT H Ω Tω × BH l
  let T1 := Σ p : (Σ ω : Ω, Tω ω.1), BH l
  let T2 := Σ p : (Σ ω : Ω, Tω ω.1), (Σ κ : Λω p.1.1, Fin (mE p.1.1 l κ) × Bω p.1.1 κ)
  let T2' := Σ q : (Σ ω : Ω, Σ κ : Λω ω.1, Fin (mE ω.1 l κ)), (Tω q.1.1 × Bω q.1.1 q.2.1)
  let T3 := Σ q : (Σ ω : Ω, Σ κ : Λω ω.1, Fin (mE ω.1 l κ)),
    (Σ ν : ΛH, AdBasM (Bω q.1.1) (fun κ ν => mL q.1.1 ν κ) ν × Fin (mL q.1.1 ν q.2.1))
  let T3' := Σ r : (Σ ν : ΛH, KM Ω mL mE (Λω := Λω) l ν),
    AdBasM (Bω r.2.1.1) (fun κ ν => mL r.2.1.1 ν κ) r.1
  let T4' := Σ r : (Σ ν : ΛH, KM Ω mL mE (Λω := Λω) l ν), BH r.1
  let T4 := NOutM Ω BH mL mE (Λω := Λω) l
  let f1 : T1 → T0 := fun p =>
    (⟨((p.1.2 : H) : G) * (p.1.1 : G), ⟨p.1.1.1, p.1.1.2, p.1.2.1, p.1.2.2, rfl⟩⟩, p.2)
  have hf1_bij : Function.Bijective f1 := by
    constructor
    · rintro ⟨⟨ω₁, a₁⟩, P₁⟩ ⟨⟨ω₂, a₂⟩, P₂⟩ heq
      have hfst := congrArg Prod.fst heq
      have hsnd := congrArg Prod.snd heq
      have hsub : ((a₁ : H) : G) * (ω₁ : G) = ((a₂ : H) : G) * (ω₂ : G) :=
        congrArg Subtype.val hfst
      let t : mackeyT H Ω Tω := ⟨((a₂ : H) : G) * (ω₂ : G), ⟨ω₂.1, ω₂.2, a₂.1, a₂.2, rfl⟩⟩
      have hu := mackeyT_decomp H Ω hΩ Tω t
      have hp12 := (hu.unique (y₁ := ⟨ω₁, a₁⟩) (y₂ := ⟨ω₂, a₂⟩) hsub rfl)
      cases hp12
      cases hsnd
      rfl
    · rintro ⟨t, P⟩
      obtain ⟨⟨ω, a⟩, hwa, _⟩ := mackeyT_decomp H Ω hΩ Tω t
      refine ⟨⟨⟨ω, a⟩, P⟩, Prod.ext (Subtype.ext hwa) rfl⟩
  let e1 : T1 ≃ T0 := Equiv.ofBijective f1 hf1_bij
  let e2 : T2' ≃ T2 :=
    { toFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2.1, x.1.2.2, x.2.2⟩⟩
      invFun := fun y => ⟨⟨y.1.1, ⟨y.2.1, y.2.2.1⟩⟩, ⟨y.1.2, y.2.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e3 : T3' ≃ T3 :=
    { toFun := fun ⟨⟨ν, ω, κ, m, e⟩, Qt⟩ => ⟨⟨ω, κ, e⟩, ν, Qt, m⟩
      invFun := fun ⟨⟨ω, κ, e⟩, ν, Qt, m⟩ => ⟨⟨ν, ω, κ, m, e⟩, Qt⟩
      left_inv := fun x => by rcases x with ⟨⟨_, _, _, _, _⟩, _⟩; rfl
      right_inv := fun x => by rcases x with ⟨⟨_, _, _⟩, _, _, _⟩; rfl }
  let e4 : T4 ≃ T4' :=
    { toFun := fun ⟨ν, Q, x⟩ => ⟨⟨ν, x⟩, Q⟩
      invFun := fun ⟨⟨ν, x⟩, Q⟩ => ⟨ν, Q, x⟩
      left_inv := fun x => by rcases x with ⟨_, _, _⟩; rfl
      right_inv := fun x => by rcases x with ⟨⟨_, _⟩, _⟩; rfl }
  let N1 : Matrix T1 T0 ℂ := permMatrix e1
  let N2 : Matrix T2 T1 ℂ := blockDiagMat (fun p : (Σ ω : Ω, Tω ω.1) => (Emat p.1.1 l)ᴴ)
  let P2 : Matrix T2' T2 ℂ := permMatrix e2
  let N3 : Matrix T3 T2' ℂ :=
    blockDiagMat (fun q : (Σ ω : Ω, Σ κ : Λω ω.1, Fin (mE ω.1 l κ)) =>
      UIndMultT (Tω q.1.1) (Bω q.1.1) (fun κ ν => mL q.1.1 ν κ)
        (RHadM BH Bω mL Lmat RH q.1.1) q.2.1)
  let P3 : Matrix T3' T3 ℂ := permMatrix e3
  let N4 : Matrix T4' T3' ℂ :=
    blockDiagMat (fun r : (Σ ν : ΛH, KM Ω mL mE (Λω := Λω) l ν) => Lmat r.2.1.1 r.1)
  let P4 : Matrix T4 T4' ℂ := permMatrix e4
  have hN1 := permMatrix_isUnitary e1
  have hN2 : N2 * N2ᴴ = 1 ∧ N2ᴴ * N2 = 1 := by
    have h := blockDiagMat_isUnitary (fun p : (Σ ω : Ω, Tω ω.1) => (Emat p.1.1 l)ᴴ) fun p => by
      have hEp := hE p.1.1 p.1.2 l
      exact ⟨by rw [Matrix.conjTranspose_conjTranspose]; convert hEp.2.1,
        by rw [Matrix.conjTranspose_conjTranspose]; convert hEp.1⟩
    exact ⟨by convert h.1, by convert h.2⟩
  have hP2 := permMatrix_isUnitary e2
  have hN3 : N3 * N3ᴴ = 1 ∧ N3ᴴ * N3 = 1 := by
    have h := blockDiagMat_isUnitary
      (fun q : (Σ ω : Ω, Σ κ : Λω ω.1, Fin (mE ω.1 l κ)) =>
        UIndMultT (Tω q.1.1) (Bω q.1.1) (fun κ ν => mL q.1.1 ν κ)
          (RHadM BH Bω mL Lmat RH q.1.1) q.2.1)
      fun q => by
        have hu := uindMultT_isUnitary (interSub H q.1.1) (Tω q.1.1) (hTω q.1.1 q.1.2)
          (Bω q.1.1) (fun κ ν => mL q.1.1 ν κ) (Rω q.1.1) (hRω q.1.1 q.1.2)
          (RHadM BH Bω mL Lmat RH q.1.1)
          (rHadM_isIrrepSystem H Ω BH RH hRH Bω Rω mL Lmat hL q.1.1 q.1.2)
          (rHadM_isAdaptedMult H Ω BH RH Bω Rω mL Lmat hL q.1.1 q.1.2) q.2.1
        exact ⟨by convert hu.1, by convert hu.2⟩
    exact ⟨by convert h.1, by convert h.2⟩
  have hP3 := permMatrix_isUnitary e3
  have hN4 : N4 * N4ᴴ = 1 ∧ N4ᴴ * N4 = 1 := by
    have h := blockDiagMat_isUnitary
      (fun r : (Σ ν : ΛH, KM Ω mL mE (Λω := Λω) l ν) => Lmat r.2.1.1 r.1) fun r => by
        have hLr := hL r.2.1.1 r.2.1.2 r.1
        exact ⟨by convert hLr.1, by convert hLr.2.1⟩
    exact ⟨by convert h.1, by convert h.2⟩
  have hP4 := permMatrix_isUnitary e4
  have hprod_unit :
      (P4 * N4 * P3 * N3 * P2 * N2 * N1) * (P4 * N4 * P3 * N3 * P2 * N2 * N1)ᴴ = 1 ∧
        (P4 * N4 * P3 * N3 * P2 * N2 * N1)ᴴ * (P4 * N4 * P3 * N3 * P2 * N2 * N1) = 1 := by
    have h1 : (N2 * N1) * (N2 * N1)ᴴ = 1 ∧ (N2 * N1)ᴴ * (N2 * N1) = 1 := by
      have h := mul_isUnitary hN2.1 (by convert hN2.2) (by convert hN1.1) (by convert hN1.2)
      exact ⟨by convert h.1, by convert h.2⟩
    have h2 : (P2 * (N2 * N1)) * (P2 * (N2 * N1))ᴴ = 1 ∧
        (P2 * (N2 * N1))ᴴ * (P2 * (N2 * N1)) = 1 := by
      have h := mul_isUnitary hP2.1 (by convert hP2.2) (by convert h1.1) (by convert h1.2)
      exact ⟨by convert h.1, by convert h.2⟩
    have h3 : (N3 * (P2 * (N2 * N1))) * (N3 * (P2 * (N2 * N1)))ᴴ = 1 ∧
        (N3 * (P2 * (N2 * N1)))ᴴ * (N3 * (P2 * (N2 * N1))) = 1 := by
      have h := mul_isUnitary hN3.1 (by convert hN3.2) (by convert h2.1) (by convert h2.2)
      exact ⟨by convert h.1, by convert h.2⟩
    have h4 : (P3 * (N3 * (P2 * (N2 * N1)))) * (P3 * (N3 * (P2 * (N2 * N1))))ᴴ = 1 ∧
        (P3 * (N3 * (P2 * (N2 * N1))))ᴴ * (P3 * (N3 * (P2 * (N2 * N1)))) = 1 := by
      have h := mul_isUnitary hP3.1 (by convert hP3.2) (by convert h3.1) (by convert h3.2)
      exact ⟨by convert h.1, by convert h.2⟩
    have h5 : (N4 * (P3 * (N3 * (P2 * (N2 * N1))))) *
        (N4 * (P3 * (N3 * (P2 * (N2 * N1)))))ᴴ = 1 ∧
        (N4 * (P3 * (N3 * (P2 * (N2 * N1)))))ᴴ *
          (N4 * (P3 * (N3 * (P2 * (N2 * N1))))) = 1 := by
      have h := mul_isUnitary hN4.1 (by convert hN4.2) (by convert h4.1) (by convert h4.2)
      exact ⟨by convert h.1, by convert h.2⟩
    have h6 := mul_isUnitary hP4.1 (by convert hP4.2) (by convert h5.1) (by convert h5.2)
    simpa only [Matrix.mul_assoc] using h6
  have hnop_eq : NopM H Ω Tω BH Bω RH mL Lmat mE Emat l = P4 * N4 * P3 * N3 * P2 * N2 * N1 := by
    ext ⟨ν, Q, ⟨ω, κ, m, e⟩⟩ ⟨t, P⟩
    have h21 : ∀ (a : Tω ω.1) (Pt : Bω ω.1 κ),
        (P2 * (N2 * N1)) ⟨⟨ω, κ, e⟩, a, Pt⟩ (t, P) =
          if ((a : H) : G) * (ω : G) = (t : G) then conj (Emat ω.1 l P ⟨κ, e, Pt⟩) else 0 := by
      intro a Pt
      rw [permMatrix_mul, blockDiagMat_mul]
      have he2 : e2 ⟨⟨ω, κ, e⟩, a, Pt⟩ = ⟨⟨ω, a⟩, ⟨κ, e, Pt⟩⟩ := rfl
      have he1 : ∀ P' : BH l,
          e1 ⟨⟨ω, a⟩, P'⟩ = (⟨((a : H) : G) * (ω : G), ⟨ω.1, ω.2, a.1, a.2, rfl⟩⟩, P') :=
        fun P' => Equiv.ofBijective_apply f1 hf1_bij ⟨⟨ω, a⟩, P'⟩
      rw [he2, Finset.sum_eq_single P]
      · dsimp only [N1, permMatrix]
        simp only [Matrix.of_apply, Matrix.conjTranspose_apply, he1]
        by_cases ha : ((a : H) : G) * (ω : G) = (t : G)
        · have hsub : (⟨((a : H) : G) * (ω : G), ⟨ω.1, ω.2, a.1, a.2, rfl⟩⟩, P) = (t, P) :=
            Prod.ext (Subtype.ext ha) rfl
          rw [if_pos hsub, mul_one, if_pos ha]
          rfl
        · have hsub : (⟨((a : H) : G) * (ω : G), ⟨ω.1, ω.2, a.1, a.2, rfl⟩⟩, P) ≠ (t, P) := by
            intro heq
            exact ha (congrArg (fun x => (x.1 : G)) heq)
          rw [if_neg hsub, mul_zero, if_neg ha]
      · intro P' _ hP'
        have hne : (⟨((a : H) : G) * (ω : G), ⟨ω.1, ω.2, a.1, a.2, rfl⟩⟩, P') ≠ (t, P) := by
          intro heq
          exact hP' (congrArg Prod.snd heq)
        dsimp only [N1, permMatrix]
        simp only [Matrix.of_apply, Matrix.conjTranspose_apply, he1, if_neg hne, mul_zero]
      · intro hP; exact False.elim (hP (Finset.mem_univ _))
    have h321 : ∀ (Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν),
        (N3 * (P2 * (N2 * N1))) ⟨⟨ω, κ, e⟩, ν, Qt, m⟩ (t, P) =
          if h : ∃ a : Tω ω.1, ((a : H) : G) * (ω : G) = (t : G) then
            ∑ Pt : Bω ω.1 κ,
              UIndMultT (Tω ω.1) (Bω ω.1) (fun κ ν => mL ω.1 ν κ)
                (RHadM BH Bω mL Lmat RH ω.1) κ
                ⟨ν, Qt, m⟩ (Classical.choose h, Pt) *
                conj (Emat ω.1 l P ⟨κ, e, Pt⟩)
          else 0 := by
      intro Qt
      rw [blockDiagMat_mul, Fintype.sum_prod_type]
      by_cases h : ∃ a : Tω ω.1, ((a : H) : G) * (ω : G) = (t : G)
      · rw [dif_pos h]
        let a₀ := Classical.choose h
        have ha₀ : ((a₀ : H) : G) * (ω : G) = (t : G) := Classical.choose_spec h
        rw [Finset.sum_eq_single a₀]
        · refine Finset.sum_congr rfl fun Pt _ => ?_
          rw [h21 a₀ Pt, if_pos ha₀]
        · intro a _ ha
          refine Finset.sum_eq_zero fun Pt _ => ?_
          have hne : ((a : H) : G) * (ω : G) ≠ (t : G) := by
            intro heq
            apply ha
            apply Subtype.ext
            exact Subtype.ext (mul_right_cancel (heq.trans ha₀.symm))
          rw [h21 a Pt, if_neg hne, mul_zero]
        · intro ha; exact False.elim (ha (Finset.mem_univ _))
      · rw [dif_neg h]
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun Pt _ => ?_
        have hne : ((a : H) : G) * (ω : G) ≠ (t : G) := fun heq => h ⟨a, heq⟩
        rw [h21 a Pt, if_neg hne, mul_zero]
    have hrhs : (P4 * N4 * P3 * N3 * P2 * N2 * N1) ⟨ν, Q, ⟨ω, κ, m, e⟩⟩ (t, P) =
        (P4 * (N4 * (P3 * (N3 * (P2 * (N2 * N1)))))) ⟨ν, Q, ⟨ω, κ, m, e⟩⟩ (t, P) := by
      simp only [Matrix.mul_assoc]
    have he4 : e4 ⟨ν, Q, ⟨ω, κ, m, e⟩⟩ = ⟨⟨ν, ⟨ω, κ, m, e⟩⟩, Q⟩ := rfl
    rw [hrhs, permMatrix_mul, he4, blockDiagMat_mul]
    have hstep3 : ∀ Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν,
        (P3 * (N3 * (P2 * (N2 * N1)))) ⟨⟨ν, ⟨ω, κ, m, e⟩⟩, Qt⟩ (t, P) =
          (N3 * (P2 * (N2 * N1))) ⟨⟨ω, κ, e⟩, ν, Qt, m⟩ (t, P) := by
      intro Qt
      rw [permMatrix_mul]
      rfl
    by_cases h : ∃ a : Tω ω.1, ((a : H) : G) * (ω : G) = (t : G)
    · have hsum_pos :
          ∑ Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν,
            Lmat ω.1 ν Q Qt * (P3 * (N3 * (P2 * (N2 * N1)))) ⟨⟨ν, ⟨ω, κ, m, e⟩⟩, Qt⟩ (t, P) =
          ∑ Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν,
            Lmat ω.1 ν Q Qt *
              ∑ Pt : Bω ω.1 κ,
                UIndMultT (Tω ω.1) (Bω ω.1) (fun κ ν => mL ω.1 ν κ)
                  (RHadM BH Bω mL Lmat RH ω.1) κ
                  ⟨ν, Qt, m⟩ (Classical.choose h, Pt) *
                  conj (Emat ω.1 l P ⟨κ, e, Pt⟩) := by
        refine Finset.sum_congr rfl fun Qt _ => ?_
        rw [hstep3 Qt, h321 Qt, dif_pos h]
      rw [hsum_pos]
      simp only [NopM, Matrix.of_apply, dif_pos h]
      have hcard_ad : Fintype.card (AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν) =
          Fintype.card (BH ν) := by
        have hL1 : Lmat ω.1 ν * (Lmat ω.1 ν)ᴴ = 1 := by convert (hL ω.1 ω.2 ν).1
        have hL2 : (Lmat ω.1 ν)ᴴ * Lmat ω.1 ν = 1 := by convert (hL ω.1 ω.2 ν).2.1
        exact (card_eq_of_isUnitary hL1 hL2).symm
      have hcard_T : Fintype.card (Tω ω.1) = (interSub H ω.1).index :=
        complement_card_eq_index (interSub H ω.1) (Tω ω.1) (hTω ω.1 ω.2)
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun Pt _ => ?_
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      congr 1
      have hterm : ∀ Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν,
          Lmat ω.1 ν Q Qt *
            UIndMultT (Tω ω.1) (Bω ω.1) (fun κ ν => mL ω.1 ν κ)
              (RHadM BH Bω mL Lmat RH ω.1) κ
              ⟨ν, Qt, m⟩ (Classical.choose h, Pt) =
          (Real.sqrt ((Fintype.card (BH ν) : ℝ) /
              ((Fintype.card (Bω ω.1 κ) : ℝ) * ((interSub H ω.1).index : ℝ))) : ℂ) *
            (Lmat ω.1 ν Q Qt *
              RHadM BH Bω mL Lmat RH ω.1 ν ((Classical.choose h : Tω ω.1) : H) Qt ⟨κ, m, Pt⟩) := by
        intro Qt
        simp only [UIndMultT, Matrix.of_apply, hcard_ad, hcard_T]
        ring
      have hsum_congr_r :
          ∑ Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν,
            Lmat ω.1 ν Q Qt *
              UIndMultT (Tω ω.1) (Bω ω.1) (fun κ ν => mL ω.1 ν κ)
                (RHadM BH Bω mL Lmat RH ω.1) κ
                ⟨ν, Qt, m⟩ (Classical.choose h, Pt) =
          (Real.sqrt ((Fintype.card (BH ν) : ℝ) /
              ((Fintype.card (Bω ω.1 κ) : ℝ) * ((interSub H ω.1).index : ℝ))) : ℂ) *
            ∑ Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν,
              Lmat ω.1 ν Q Qt *
                RHadM BH Bω mL Lmat RH ω.1 ν ((Classical.choose h : Tω ω.1) : H) Qt ⟨κ, m, Pt⟩ := by
        rw [Finset.sum_congr rfl fun Qt _ => hterm Qt, ← Finset.mul_sum]
      rw [hsum_congr_r]
      congr 1
      have hL1 : Lmat ω.1 ν * (Lmat ω.1 ν)ᴴ = 1 := by convert (hL ω.1 ω.2 ν).1
      calc (RH ν ((Classical.choose h : Tω ω.1) : H) * Lmat ω.1 ν) Q ⟨κ, m, Pt⟩
          = ((Lmat ω.1 ν * (Lmat ω.1 ν)ᴴ) *
              (RH ν ((Classical.choose h : Tω ω.1) : H) * Lmat ω.1 ν)) Q ⟨κ, m, Pt⟩ := by
              rw [hL1, Matrix.one_mul]
        _ = (Lmat ω.1 ν *
              RHadM BH Bω mL Lmat RH ω.1 ν ((Classical.choose h : Tω ω.1) : H)) Q ⟨κ, m, Pt⟩ := by
              simp only [RHadM, Matrix.mul_assoc]
        _ = ∑ Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν,
              Lmat ω.1 ν Q Qt *
                RHadM BH Bω mL Lmat RH ω.1 ν ((Classical.choose h : Tω ω.1) : H) Qt ⟨κ, m, Pt⟩ := by
              rw [Matrix.mul_apply]
    · have hsum_neg :
          ∑ Qt : AdBasM (Bω ω.1) (fun κ ν => mL ω.1 ν κ) ν,
            Lmat ω.1 ν Q Qt * (P3 * (N3 * (P2 * (N2 * N1)))) ⟨⟨ν, ⟨ω, κ, m, e⟩⟩, Qt⟩ (t, P) = 0 := by
        refine Finset.sum_eq_zero fun Qt _ => ?_
        rw [hstep3 Qt, h321 Qt, dif_neg h, mul_zero]
      rw [hsum_neg]
      simp only [NopM, Matrix.of_apply, dif_neg h]
  rw [hnop_eq]
  exact hprod_unit

/-! ### Section 5: Proof of `AopM * NopM = UIndMult` and unitarity of `AblockM` -/

private lemma aopM_mul_nopM {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (mult : ΛH → ΛG → ℕ)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (_hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBasM BH mult μ) (AdBasM BH mult μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsAdaptedMult H BH mult RH RG)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (mL : ∀ ω, ΛH → Λω ω → ℕ)
    (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
    (hL : ∀ ω ∈ Ω, ∀ ν, IsEmbeddingFamily H Bω (fun h => RH ν (h : H)) (mL ω ν) (Rω ω)
      (Lmat ω ν))
    (mE : ∀ ω, ΛH → Λω ω → ℕ)
    (Emat : ∀ ω l, Matrix (BH l) (Σ κ : Λω ω, Fin (mE ω l κ) × Bω ω κ) ℂ)
    (hE : ∀ ω ∈ Ω, ∀ l, IsEmbeddingFamily H Bω (twistRep H ω (RH l)) (mE ω l) (Rω ω) (Emat ω l))
    (l : ΛH) :
    AopM H Ω BH mult Bω RG mL Lmat mE Emat l * NopM H Ω Tω BH Bω RH mL Lmat mE Emat l =
      UIndMult H Ω Tω BH mult RG l := by
  ext ⟨μ, ⟨ν, r, Q⟩, b⟩ ⟨t, P⟩
  obtain ⟨⟨ω₀', a₀⟩, ha₀, huniq⟩ := mackeyT_decomp H Ω hΩ Tω t
  rcases ω₀' with ⟨ω₀, hω₀⟩
  have ha₀' : ((a₀ : H) : G) * ω₀ = (t : G) := ha₀
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single ν]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single Q]
    · have hAop : ∀ x : KM Ω mL mE (Λω := Λω) l ν,
          AopM H Ω BH mult Bω RG mL Lmat mE Emat l ⟨μ, ⟨ν, r, Q⟩, b⟩ ⟨ν, Q, x⟩ =
            AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν ⟨μ, r, b⟩ x := by
        intro x
        simp [AopM]
      simp_rw [hAop]
      rw [Fintype.sum_sigma, Finset.sum_eq_single ⟨ω₀, hω₀⟩]
      · have hex_a : ∃ a : Tω ω₀, ((a : H) : G) * ω₀ = (t : G) := ⟨a₀, ha₀'⟩
        have hch_a : Classical.choose hex_a = a₀ := by
          have hu := huniq ⟨⟨ω₀, hω₀⟩, Classical.choose hex_a⟩ (Classical.choose_spec hex_a)
          exact eq_of_heq (Sigma.ext_iff.mp hu).2
        let Tmat : Matrix (BH ν) (BH l) ℂ := Matrix.of fun Q' P' =>
          RG μ ω₀ ⟨ν, r, Q'⟩ ⟨l, b, P'⟩
        let Wmat : Matrix (Σ κ : Λω ω₀, Fin (mL ω₀ ν κ) × Bω ω₀ κ)
            (Σ κ : Λω ω₀, Fin (mE ω₀ l κ) × Bω ω₀ κ) ℂ :=
          (Lmat ω₀ ν)ᴴ * Tmat * Emat ω₀ l
        have hT_inter : ∀ h : interSub H ω₀,
            RH ν (h : H) * Tmat = Tmat * twistRep H ω₀ (RH l) h := by
          intro h
          ext Q' P'
          have had1 : (RH ν (h : H) * Tmat) Q' P' =
              RG μ (((h : H) : G) * ω₀) ⟨ν, r, Q'⟩ ⟨l, b, P'⟩ := by
            rw [Matrix.mul_apply, (hRG.1 μ).1.2 ((h : H) : G) ω₀, Matrix.mul_apply,
              Fintype.sum_sigma, Finset.sum_eq_single ν]
            · rw [Fintype.sum_prod_type, Finset.sum_eq_single r]
              · refine Finset.sum_congr rfl fun Q'' _ => ?_
                have := hAd μ (h : H) ⟨ν, r, Q'⟩ ⟨ν, r, Q''⟩
                dsimp only at this
                rw [dif_pos rfl] at this
                dsimp only [cast_eq] at this
                rw [if_pos rfl] at this
                rw [this]
                rfl
              · intro r' _ hr'
                refine Finset.sum_eq_zero fun Q'' _ => ?_
                have := hAd μ (h : H) ⟨ν, r, Q'⟩ ⟨ν, r', Q''⟩
                dsimp only at this
                rw [dif_pos rfl] at this
                dsimp only [cast_eq] at this
                rw [if_neg (Ne.symm hr')] at this
                rw [this, zero_mul]
              · intro hr'; exact False.elim (hr' (Finset.mem_univ _))
            · intro ν' _ hν'
              refine Finset.sum_eq_zero fun rQ'' _ => ?_
              have := hAd μ (h : H) ⟨ν, r, Q'⟩ ⟨ν', rQ''⟩
              dsimp only at this
              rw [dif_neg (Ne.symm hν')] at this
              rw [this, zero_mul]
            · intro hν'; exact False.elim (hν' (Finset.mem_univ _))
          have had2 : (Tmat * twistRep H ω₀ (RH l) h) Q' P' =
              RG μ (ω₀ * (ω₀⁻¹ * ((h : H) : G) * ω₀)) ⟨ν, r, Q'⟩ ⟨l, b, P'⟩ := by
            let h' : H := ⟨ω₀⁻¹ * ((h : H) : G) * ω₀, interSub_conj_mem H ω₀ h⟩
            rw [Matrix.mul_apply, (hRG.1 μ).1.2 ω₀ (h' : G), Matrix.mul_apply,
              Fintype.sum_sigma, Finset.sum_eq_single l]
            · rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
              · refine Finset.sum_congr rfl fun P'' _ => ?_
                have := hAd μ h' ⟨l, b, P''⟩ ⟨l, b, P'⟩
                dsimp only at this
                rw [dif_pos rfl] at this
                dsimp only [cast_eq] at this
                rw [if_pos rfl] at this
                rw [this]
                rfl
              · intro b' _ hb'
                refine Finset.sum_eq_zero fun P'' _ => ?_
                have := hAd μ h' ⟨l, b', P''⟩ ⟨l, b, P'⟩
                dsimp only at this
                rw [dif_pos rfl] at this
                dsimp only [cast_eq] at this
                rw [if_neg hb'] at this
                rw [this, mul_zero]
              · intro hb'; exact False.elim (hb' (Finset.mem_univ _))
            · intro l' _ hl'
              refine Finset.sum_eq_zero fun bP'' _ => ?_
              have := hAd μ h' ⟨l', bP''⟩ ⟨l, b, P'⟩
              dsimp only at this
              rw [dif_neg hl'] at this
              rw [this, mul_zero]
            · intro hl'; exact False.elim (hl' (Finset.mem_univ _))
          have hconj_eq : ((h : H) : G) * ω₀ = ω₀ * (ω₀⁻¹ * ((h : H) : G) * ω₀) := by
            simp only [← mul_assoc, mul_inv_cancel, one_mul]
          rw [had1, had2, hconj_eq]
        have hW_inter : ∀ h : interSub H ω₀,
            blockRep H Bω (mL ω₀ ν) (Rω ω₀) h * Wmat =
              Wmat * blockRep H Bω (mE ω₀ l) (Rω ω₀) h := by
          intro h
          have hL1 : Lmat ω₀ ν * (Lmat ω₀ ν)ᴴ = 1 := by convert (hL ω₀ hω₀ ν).1
          have hL2 : (Lmat ω₀ ν)ᴴ * Lmat ω₀ ν = 1 := by convert (hL ω₀ hω₀ ν).2.1
          have hL_adj : blockRep H Bω (mL ω₀ ν) (Rω ω₀) h * (Lmat ω₀ ν)ᴴ =
              (Lmat ω₀ ν)ᴴ * RH ν (h : H) := by
            calc blockRep H Bω (mL ω₀ ν) (Rω ω₀) h * (Lmat ω₀ ν)ᴴ
                = ((Lmat ω₀ ν)ᴴ * Lmat ω₀ ν) * blockRep H Bω (mL ω₀ ν) (Rω ω₀) h *
                    (Lmat ω₀ ν)ᴴ := by rw [hL2, Matrix.one_mul]
              _ = (Lmat ω₀ ν)ᴴ * (Lmat ω₀ ν * blockRep H Bω (mL ω₀ ν) (Rω ω₀) h) *
                    (Lmat ω₀ ν)ᴴ := by simp only [Matrix.mul_assoc]
              _ = (Lmat ω₀ ν)ᴴ * (RH ν (h : H) * Lmat ω₀ ν) * (Lmat ω₀ ν)ᴴ := by
                    rw [(hL ω₀ hω₀ ν).2.2 h]
              _ = (Lmat ω₀ ν)ᴴ * RH ν (h : H) * (Lmat ω₀ ν * (Lmat ω₀ ν)ᴴ) := by
                    simp only [Matrix.mul_assoc]
              _ = (Lmat ω₀ ν)ᴴ * RH ν (h : H) := by rw [hL1, Matrix.mul_one]
          calc blockRep H Bω (mL ω₀ ν) (Rω ω₀) h * Wmat
              = (blockRep H Bω (mL ω₀ ν) (Rω ω₀) h * (Lmat ω₀ ν)ᴴ) * Tmat * Emat ω₀ l := by
                  simp only [Wmat, Matrix.mul_assoc]
            _ = (Lmat ω₀ ν)ᴴ * (RH ν (h : H) * Tmat) * Emat ω₀ l := by
                  rw [hL_adj]; simp only [Matrix.mul_assoc]
            _ = (Lmat ω₀ ν)ᴴ * (Tmat * twistRep H ω₀ (RH l) h) * Emat ω₀ l := by
                  rw [hT_inter h]
            _ = (Lmat ω₀ ν)ᴴ * Tmat * (Emat ω₀ l * blockRep H Bω (mE ω₀ l) (Rω ω₀) h) := by
                  simp only [Matrix.mul_assoc, ← (hE ω₀ hω₀ l).2.2 h]
            _ = Wmat * blockRep H Bω (mE ω₀ l) (Rω ω₀) h := by
                  simp only [Wmat, Matrix.mul_assoc]
        have hW_block_inter : ∀ (κ : Λω ω₀) (m : Fin (mL ω₀ ν κ))
            (κ' : Λω ω₀) (e : Fin (mE ω₀ l κ')) (h : interSub H ω₀),
            Rω ω₀ κ h * Matrix.of (fun Pt Pt' => Wmat ⟨κ, m, Pt⟩ ⟨κ', e, Pt'⟩) =
              Matrix.of (fun Pt Pt' => Wmat ⟨κ, m, Pt⟩ ⟨κ', e, Pt'⟩) * Rω ω₀ κ' h := by
          intro κ m κ' e h
          ext Pt Pt'
          have hwe := congr_fun (congr_fun (hW_inter h) ⟨κ, m, Pt⟩) ⟨κ', e, Pt'⟩
          have hlhs : (blockRep H Bω (mL ω₀ ν) (Rω ω₀) h * Wmat) ⟨κ, m, Pt⟩ ⟨κ', e, Pt'⟩ =
              (Rω ω₀ κ h * Matrix.of (fun Pt₁ Pt₂ => Wmat ⟨κ, m, Pt₁⟩ ⟨κ', e, Pt₂⟩)) Pt Pt' := by
            rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single κ]
            · rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
              · simp [blockRep, Matrix.mul_apply]
              · intro m' _ hm'
                refine Finset.sum_eq_zero fun Pt₁ _ => ?_
                simp [blockRep, hm'.symm]
              · intro hm; exact False.elim (hm (Finset.mem_univ _))
            · intro κ₁ _ hκ₁
              refine Finset.sum_eq_zero fun mPt₁ _ => ?_
              simp [blockRep, hκ₁.symm]
            · intro hκ; exact False.elim (hκ (Finset.mem_univ _))
          have hrhs : (Wmat * blockRep H Bω (mE ω₀ l) (Rω ω₀) h) ⟨κ, m, Pt⟩ ⟨κ', e, Pt'⟩ =
              (Matrix.of (fun Pt₁ Pt₂ => Wmat ⟨κ, m, Pt₁⟩ ⟨κ', e, Pt₂⟩) * Rω ω₀ κ' h) Pt Pt' := by
            rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single κ']
            · rw [Fintype.sum_prod_type, Finset.sum_eq_single e]
              · simp [blockRep, Matrix.mul_apply]
              · intro e' _ he'
                refine Finset.sum_eq_zero fun Pt₂ _ => ?_
                simp [blockRep, he']
              · intro he; exact False.elim (he (Finset.mem_univ _))
            · intro κ₂ _ hκ₂
              refine Finset.sum_eq_zero fun ePt₂ _ => ?_
              simp [blockRep, hκ₂]
            · intro hκ'; exact False.elim (hκ' (Finset.mem_univ _))
          rw [← hlhs, ← hrhs, hwe]
        have hW_ne : ∀ (κ : Λω ω₀) (m : Fin (mL ω₀ ν κ)) (κ' : Λω ω₀) (e : Fin (mE ω₀ l κ')),
            κ ≠ κ' → ∀ Pt Pt', Wmat ⟨κ, m, Pt⟩ ⟨κ', e, Pt'⟩ = 0 := by
          intro κ m κ' e hne Pt Pt'
          have h0 := schur_zero_of_not_repEquiv ((hRω ω₀ hω₀).2.1 κ') ((hRω ω₀ hω₀).2.1 κ)
            ((hRω ω₀ hω₀).2.2.1 κ' κ (Ne.symm hne)) (hW_block_inter κ m κ' e)
          simpa using congr_fun (congr_fun h0 Pt) Pt'
        have hW_eq : ∀ (κ : Λω ω₀) (m : Fin (mL ω₀ ν κ)) (e : Fin (mE ω₀ l κ))
            (Pt Pt' : Bω ω₀ κ),
            ((Fintype.card (Bω ω₀ κ) : ℂ)⁻¹ *
                ∑ Pt'' : Bω ω₀ κ, Wmat ⟨κ, m, Pt''⟩ ⟨κ, e, Pt''⟩) *
              (if Pt = Pt' then 1 else 0) =
              Wmat ⟨κ, m, Pt⟩ ⟨κ, e, Pt'⟩ := by
          intro κ m e Pt Pt'
          obtain ⟨c, hc⟩ := schur_eq_smul_one ((hRω ω₀ hω₀).2.1 κ) (hW_block_inter κ m κ e)
          have htr : ∑ Pt'' : Bω ω₀ κ, Wmat ⟨κ, m, Pt''⟩ ⟨κ, e, Pt''⟩ =
              c * (Fintype.card (Bω ω₀ κ) : ℂ) := by
            have htr' := congrArg Matrix.trace hc
            simpa [Matrix.trace, Matrix.diag, mul_comm] using htr'
          have hd_ne : (Fintype.card (Bω ω₀ κ) : ℂ) ≠ 0 := by
            have : Nonempty (Bω ω₀ κ) := ((hRω ω₀ hω₀).2.1 κ).1
            exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
          have hc_eq : (Fintype.card (Bω ω₀ κ) : ℂ)⁻¹ *
              ∑ Pt'' : Bω ω₀ κ, Wmat ⟨κ, m, Pt''⟩ ⟨κ, e, Pt''⟩ = c := by
            rw [htr, mul_comm c _, ← mul_assoc, inv_mul_cancel₀ hd_ne, one_mul]
          rw [hc_eq]
          have hpt := congr_fun (congr_fun hc Pt) Pt'
          simpa [Matrix.smul_apply, Matrix.one_apply] using hpt.symm
        have hsum_κ :
            ∑ x : Σ κ : Λω ω₀, Fin (mL ω₀ ν κ) × Bω ω₀ κ,
              ∑ y : Σ κ' : Λω ω₀, Fin (mE ω₀ l κ') × Bω ω₀ κ',
                (RH ν (a₀ : H) * Lmat ω₀ ν) Q x * Wmat x y * conj (Emat ω₀ l P y) =
            ∑ κ : Λω ω₀, ∑ m : Fin (mL ω₀ ν κ), ∑ e : Fin (mE ω₀ l κ),
              (Fintype.card (Bω ω₀ κ) : ℂ)⁻¹ *
                (∑ Pt'' : Bω ω₀ κ, Wmat ⟨κ, m, Pt''⟩ ⟨κ, e, Pt''⟩) *
                ∑ Pt : Bω ω₀ κ,
                  (RH ν (a₀ : H) * Lmat ω₀ ν) Q ⟨κ, m, Pt⟩ * conj (Emat ω₀ l P ⟨κ, e, Pt⟩) := by
          rw [Fintype.sum_sigma]
          refine Finset.sum_congr rfl fun κ _ => ?_
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun m _ => ?_
          have hy : ∀ Pt : Bω ω₀ κ,
              ∑ y : Σ κ' : Λω ω₀, Fin (mE ω₀ l κ') × Bω ω₀ κ',
                (RH ν (a₀ : H) * Lmat ω₀ ν) Q ⟨κ, m, Pt⟩ * Wmat ⟨κ, m, Pt⟩ y * conj (Emat ω₀ l P y) =
              ∑ e : Fin (mE ω₀ l κ), ∑ Pt' : Bω ω₀ κ,
                (RH ν (a₀ : H) * Lmat ω₀ ν) Q ⟨κ, m, Pt⟩ *
                  Wmat ⟨κ, m, Pt⟩ ⟨κ, e, Pt'⟩ * conj (Emat ω₀ l P ⟨κ, e, Pt'⟩) := by
            intro Pt
            rw [Fintype.sum_sigma, Finset.sum_eq_single κ]
            · rw [Fintype.sum_prod_type]
            · intro κ' _ hκ'
              refine Finset.sum_eq_zero fun ePt' _ => ?_
              rw [hW_ne κ m κ' ePt'.1 hκ'.symm Pt ePt'.2, mul_zero, zero_mul]
            · intro hκ; exact False.elim (hκ (Finset.mem_univ _))
          simp_rw [hy]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun Pt _ => ?_
          rw [Finset.sum_eq_single Pt]
          · have hpt := hW_eq κ m e Pt Pt
            rw [if_pos rfl, mul_one] at hpt
            rw [hpt]
            ring
          · intro Pt' _ hPt'
            have hpt := hW_eq κ m e Pt Pt'
            rw [if_neg hPt'.symm, mul_zero] at hpt
            rw [← hpt]
            simp
          · intro hPt; exact False.elim (hPt (Finset.mem_univ _))
        have hW_entry : ∀ (κ : Λω ω₀) (m : Fin (mL ω₀ ν κ)) (e : Fin (mE ω₀ l κ)),
            ∑ Pt'' : Bω ω₀ κ, Wmat ⟨κ, m, Pt''⟩ ⟨κ, e, Pt''⟩ =
              ∑ Pt'' : Bω ω₀ κ, ∑ Q' : BH ν, ∑ P' : BH l,
                conj (Lmat ω₀ ν Q' ⟨κ, m, Pt''⟩) * RG μ ω₀ ⟨ν, r, Q'⟩ ⟨l, b, P'⟩ *
                  Emat ω₀ l P' ⟨κ, e, Pt''⟩ := by
          intro κ m e
          refine Finset.sum_congr rfl fun Pt'' _ => ?_
          simp only [Wmat, Matrix.mul_apply, Matrix.conjTranspose_apply, Tmat, Matrix.of_apply,
            Finset.sum_mul]
          exact Finset.sum_comm
        have hpref : ∀ κ : Λω ω₀,
            (Real.sqrt (((Fintype.card (AdBasM BH mult μ) : ℝ) *
                ((interSub H ω₀).index : ℝ)) /
              ((Fintype.card (Bω ω₀ κ) : ℝ) * (Fintype.card (BH l) : ℝ) *
                (Fintype.card (BH ν) : ℝ) * (H.index : ℝ))) : ℂ) *
            (Real.sqrt ((Fintype.card (BH ν) : ℝ) /
              ((Fintype.card (Bω ω₀ κ) : ℝ) * ((interSub H ω₀).index : ℝ))) : ℂ) =
            (Real.sqrt ((Fintype.card (AdBasM BH mult μ) : ℝ) /
              ((Fintype.card (BH l) : ℝ) * (H.index : ℝ))) : ℂ) *
            (Fintype.card (Bω ω₀ κ) : ℂ)⁻¹ := by
          intro κ
          have : Nonempty (Bω ω₀ κ) := ((hRω ω₀ hω₀).2.1 κ).1
          have : Nonempty (BH ν) := ⟨Q⟩
          have : Nonempty (BH l) := ⟨P⟩
          have hdκ_pos : (0 : ℝ) < Fintype.card (Bω ω₀ κ) := Nat.cast_pos.mpr Fintype.card_pos
          have hdν_pos : (0 : ℝ) < Fintype.card (BH ν) := Nat.cast_pos.mpr Fintype.card_pos
          have hdl_pos : (0 : ℝ) < Fintype.card (BH l) := Nat.cast_pos.mpr Fintype.card_pos
          have hn_pos : (0 : ℝ) < (H.index : ℝ) :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
          have hnω_pos : (0 : ℝ) < ((interSub H ω₀).index : ℝ) :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
          have hdκ_ne : (Fintype.card (Bω ω₀ κ) : ℝ) ≠ 0 := ne_of_gt hdκ_pos
          have hinv : (Fintype.card (Bω ω₀ κ) : ℂ)⁻¹ =
              (((Fintype.card (Bω ω₀ κ) : ℝ)⁻¹ : ℝ) : ℂ) := by
            rw [Complex.ofReal_inv, Complex.ofReal_natCast]
          rw [← Complex.ofReal_mul, hinv, ← Complex.ofReal_mul]
          congr 1
          rw [← Real.sqrt_mul (by positivity)]
          have hprod :
              ((Fintype.card (AdBasM BH mult μ) : ℝ) * ((interSub H ω₀).index : ℝ)) /
                ((Fintype.card (Bω ω₀ κ) : ℝ) * (Fintype.card (BH l) : ℝ) *
                  (Fintype.card (BH ν) : ℝ) * (H.index : ℝ)) *
                ((Fintype.card (BH ν) : ℝ) /
                  ((Fintype.card (Bω ω₀ κ) : ℝ) * ((interSub H ω₀).index : ℝ))) =
              ((Fintype.card (AdBasM BH mult μ) : ℝ) /
                ((Fintype.card (BH l) : ℝ) * (H.index : ℝ))) *
                ((Fintype.card (Bω ω₀ κ) : ℝ)⁻¹ ^ 2) := by
            field_simp
          rw [hprod, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        have hLHS_collapse :
            ∑ mke : Σ κ : Λω ω₀, Fin (mL ω₀ ν κ) × Fin (mE ω₀ l κ),
              AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν ⟨μ, r, b⟩ ⟨⟨ω₀, hω₀⟩, mke⟩ *
                NopM H Ω Tω BH Bω RH mL Lmat mE Emat l ⟨ν, Q, ⟨⟨ω₀, hω₀⟩, mke⟩⟩ (t, P) =
            (Real.sqrt ((Fintype.card (AdBasM BH mult μ) : ℝ) /
              ((Fintype.card (BH l) : ℝ) * (H.index : ℝ))) : ℂ) *
              ((RH ν (a₀ : H) * Lmat ω₀ ν) * Wmat * (Emat ω₀ l)ᴴ) Q P := by
          rw [Fintype.sum_sigma]
          have hterm : ∀ κ : Λω ω₀,
              ∑ me : Fin (mL ω₀ ν κ) × Fin (mE ω₀ l κ),
                AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν ⟨μ, r, b⟩ ⟨⟨ω₀, hω₀⟩, κ, me⟩ *
                  NopM H Ω Tω BH Bω RH mL Lmat mE Emat l ⟨ν, Q, ⟨⟨ω₀, hω₀⟩, κ, me⟩⟩ (t, P) =
              (Real.sqrt ((Fintype.card (AdBasM BH mult μ) : ℝ) /
                ((Fintype.card (BH l) : ℝ) * (H.index : ℝ))) : ℂ) *
                ∑ m : Fin (mL ω₀ ν κ), ∑ e : Fin (mE ω₀ l κ),
                  (Fintype.card (Bω ω₀ κ) : ℂ)⁻¹ *
                    (∑ Pt'' : Bω ω₀ κ, Wmat ⟨κ, m, Pt''⟩ ⟨κ, e, Pt''⟩) *
                    ∑ Pt : Bω ω₀ κ,
                      (RH ν (a₀ : H) * Lmat ω₀ ν) Q ⟨κ, m, Pt⟩ * conj (Emat ω₀ l P ⟨κ, e, Pt⟩) := by
            intro κ
            rw [Fintype.sum_prod_type, Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => ?_
            simp only [AblockM, NopM, Matrix.of_apply, dif_pos hex_a, hch_a]
            rw [← hW_entry κ m e]
            have hpull :
                ∑ Pt : Bω ω₀ κ,
                  (Real.sqrt ((Fintype.card (BH ν) : ℝ) /
                      ((Fintype.card (Bω ω₀ κ) : ℝ) * ((interSub H ω₀).index : ℝ))) : ℂ) *
                    (RH ν (a₀ : H) * Lmat ω₀ ν) Q ⟨κ, m, Pt⟩ *
                    conj (Emat ω₀ l P ⟨κ, e, Pt⟩) =
                (Real.sqrt ((Fintype.card (BH ν) : ℝ) /
                    ((Fintype.card (Bω ω₀ κ) : ℝ) * ((interSub H ω₀).index : ℝ))) : ℂ) *
                  ∑ Pt : Bω ω₀ κ,
                    (RH ν (a₀ : H) * Lmat ω₀ ν) Q ⟨κ, m, Pt⟩ * conj (Emat ω₀ l P ⟨κ, e, Pt⟩) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun Pt _ => by ring
            rw [hpull]
            calc ((Real.sqrt (((Fintype.card (AdBasM BH mult μ) : ℝ) *
                    ((interSub H ω₀).index : ℝ)) /
                  ((Fintype.card (Bω ω₀ κ) : ℝ) * (Fintype.card (BH l) : ℝ) *
                    (Fintype.card (BH ν) : ℝ) * (H.index : ℝ))) : ℂ) *
                  ∑ Pt'' : Bω ω₀ κ, Wmat ⟨κ, m, Pt''⟩ ⟨κ, e, Pt''⟩) *
                ((Real.sqrt ((Fintype.card (BH ν) : ℝ) /
                    ((Fintype.card (Bω ω₀ κ) : ℝ) * ((interSub H ω₀).index : ℝ))) : ℂ) *
                  ∑ Pt : Bω ω₀ κ,
                    (RH ν (a₀ : H) * Lmat ω₀ ν) Q ⟨κ, m, Pt⟩ * conj (Emat ω₀ l P ⟨κ, e, Pt⟩))
                = ((Real.sqrt (((Fintype.card (AdBasM BH mult μ) : ℝ) *
                      ((interSub H ω₀).index : ℝ)) /
                    ((Fintype.card (Bω ω₀ κ) : ℝ) * (Fintype.card (BH l) : ℝ) *
                      (Fintype.card (BH ν) : ℝ) * (H.index : ℝ))) : ℂ) *
                    (Real.sqrt ((Fintype.card (BH ν) : ℝ) /
                      ((Fintype.card (Bω ω₀ κ) : ℝ) * ((interSub H ω₀).index : ℝ))) : ℂ)) *
                  ((∑ Pt'' : Bω ω₀ κ, Wmat ⟨κ, m, Pt''⟩ ⟨κ, e, Pt''⟩) *
                    ∑ Pt : Bω ω₀ κ,
                      (RH ν (a₀ : H) * Lmat ω₀ ν) Q ⟨κ, m, Pt⟩ * conj (Emat ω₀ l P ⟨κ, e, Pt⟩)) := by
                    ring
              _ = _ := by rw [hpref κ]; ring
          simp_rw [hterm]
          rw [← Finset.mul_sum, ← hsum_κ]
          congr 1
          rw [Matrix.mul_apply, Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
          rfl
        rw [hLHS_collapse]
        have hmat_id : ((RH ν (a₀ : H) * Lmat ω₀ ν) * Wmat * (Emat ω₀ l)ᴴ) Q P =
            RG μ (t : G) ⟨ν, r, Q⟩ ⟨l, b, P⟩ := by
          have hL1 : Lmat ω₀ ν * (Lmat ω₀ ν)ᴴ = 1 := by convert (hL ω₀ hω₀ ν).1
          have hE1 : Emat ω₀ l * (Emat ω₀ l)ᴴ = 1 := by convert (hE ω₀ hω₀ l).1
          have hw : (RH ν (a₀ : H) * Lmat ω₀ ν) * Wmat * (Emat ω₀ l)ᴴ = RH ν (a₀ : H) * Tmat := by
            calc (RH ν (a₀ : H) * Lmat ω₀ ν) * ((Lmat ω₀ ν)ᴴ * Tmat * Emat ω₀ l) * (Emat ω₀ l)ᴴ
                = RH ν (a₀ : H) * (Lmat ω₀ ν * (Lmat ω₀ ν)ᴴ) * Tmat * (Emat ω₀ l * (Emat ω₀ l)ᴴ) := by
                    simp only [Matrix.mul_assoc]
              _ = RH ν (a₀ : H) * Tmat := by
                    rw [hL1, hE1]
                    simp only [Matrix.mul_one]
          rw [hw, Matrix.mul_apply, ← ha₀', (hRG.1 μ).1.2 ((a₀ : H) : G) ω₀, Matrix.mul_apply,
            Fintype.sum_sigma, Finset.sum_eq_single ν]
          · rw [Fintype.sum_prod_type, Finset.sum_eq_single r]
            · refine Finset.sum_congr rfl fun Q' _ => ?_
              have := hAd μ (a₀ : H) ⟨ν, r, Q⟩ ⟨ν, r, Q'⟩
              dsimp only at this
              rw [dif_pos rfl] at this
              dsimp only [cast_eq] at this
              rw [if_pos rfl] at this
              rw [this]
              rfl
            · intro r' _ hr'
              refine Finset.sum_eq_zero fun Q' _ => ?_
              have := hAd μ (a₀ : H) ⟨ν, r, Q⟩ ⟨ν, r', Q'⟩
              dsimp only at this
              rw [dif_pos rfl] at this
              dsimp only [cast_eq] at this
              rw [if_neg (Ne.symm hr')] at this
              rw [this, zero_mul]
            · intro hr'; exact False.elim (hr' (Finset.mem_univ _))
          · intro ν' _ hν'
            refine Finset.sum_eq_zero fun rQ' _ => ?_
            have := hAd μ (a₀ : H) ⟨ν, r, Q⟩ ⟨ν', rQ'⟩
            dsimp only at this
            rw [dif_neg (Ne.symm hν')] at this
            rw [this, zero_mul]
          · intro hν'; exact False.elim (hν' (Finset.mem_univ _))
        rw [hmat_id]
        simp [UIndMult]
      · intro ω' _ hω'
        refine Finset.sum_eq_zero fun mke _ => ?_
        have hnot : ¬ ∃ a : Tω ω'.1, ((a : H) : G) * (ω' : G) = (t : G) := by
          rintro ⟨a, ha⟩
          have hu := huniq ⟨ω', a⟩ ha
          exact hω' (congrArg Sigma.fst hu)
        simp only [NopM, Matrix.of_apply, dif_neg hnot, mul_zero]
      · intro hω'; exact False.elim (hω' (Finset.mem_univ _))
    · intro Q' _ hQ'
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [AopM, Ne.symm hQ']
    · intro hQ; exact False.elim (hQ (Finset.mem_univ _))
  · intro ν' _ hν'
    refine Finset.sum_eq_zero fun Qx _ => ?_
    simp [AopM, Ne.symm hν']
  · intro hν; exact False.elim (hν (Finset.mem_univ _))

private lemma ablockM_isUnitary {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (mult : ΛH → ΛG → ℕ)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBasM BH mult μ) (AdBasM BH mult μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsAdaptedMult H BH mult RH RG)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type)
    [∀ ω κ, Fintype (Bω ω κ)] [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (mL : ∀ ω, ΛH → Λω ω → ℕ)
    (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
    (hL : ∀ ω ∈ Ω, ∀ ν, IsEmbeddingFamily H Bω (fun h => RH ν (h : H)) (mL ω ν) (Rω ω)
      (Lmat ω ν))
    (mE : ∀ ω, ΛH → Λω ω → ℕ)
    (Emat : ∀ ω l, Matrix (BH l) (Σ κ : Λω ω, Fin (mE ω l κ) × Bω ω κ) ℂ)
    (hE : ∀ ω ∈ Ω, ∀ l, IsEmbeddingFamily H Bω (twistRep H ω (RH l)) (mE ω l) (Rω ω) (Emat ω l))
    (l ν : ΛH) :
    AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν *
        (AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν)ᴴ = 1 ∧
      (AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν)ᴴ *
        AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν = 1 := by
  let A := AopM H Ω BH mult Bω RG mL Lmat mE Emat l
  let N := NopM H Ω Tω BH Bω RH mL Lmat mE Emat l
  let U := UIndMult H Ω Tω BH mult RG l
  have hAN : A * N = U :=
    aopM_mul_nopM H Ω hΩ Tω BH mult RH hRH RG hRG hAd Bω Rω hRω mL Lmat hL mE Emat hE l
  obtain ⟨hU1, hU2⟩ := uindMult_isUnitary H Ω hΩ Tω hTω BH mult RH hRH RG hRG hAd l
  obtain ⟨hN1, hN2⟩ := nopM_isUnitary H Ω hΩ Tω hTω BH RH hRH Bω Rω hRω mL Lmat hL mE Emat hE l
  have hA_eq : A = U * Nᴴ := by
    calc A = A * (N * Nᴴ) := by rw [hN1, Matrix.mul_one]
      _ = (A * N) * Nᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = U * Nᴴ := by rw [hAN]
  have hA_unit : A * Aᴴ = 1 ∧ Aᴴ * A = 1 := by
    rw [hA_eq]
    exact mul_isUnitary hU1 (by convert hU2)
      (by dsimp only [N]; rw [Matrix.conjTranspose_conjTranspose]; convert hN2)
      (by dsimp only [N]; rw [Matrix.conjTranspose_conjTranspose]; convert hN1)
  obtain ⟨Q₀⟩ := (hRH.2.1 ν).1
  constructor
  · ext ⟨μ₁, r₁, b₁⟩ ⟨μ₂, r₂, b₂⟩
    have hentry := congr_fun (congr_fun hA_unit.1 ⟨μ₁, ⟨ν, r₁, Q₀⟩, b₁⟩) ⟨μ₂, ⟨ν, r₂, Q₀⟩, b₂⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry ⊢
    have hred :
        ∑ o : NOutM Ω BH mL mE (Λω := Λω) l,
          A ⟨μ₁, ⟨ν, r₁, Q₀⟩, b₁⟩ o * star (A ⟨μ₂, ⟨ν, r₂, Q₀⟩, b₂⟩ o) =
        ∑ x : KM Ω mL mE (Λω := Λω) l ν,
          AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν ⟨μ₁, r₁, b₁⟩ x *
            star (AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν ⟨μ₂, r₂, b₂⟩ x) := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single ν]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single Q₀]
        · refine Finset.sum_congr rfl fun x _ => ?_
          simp [A, AopM]
        · intro Q' _ hQ'
          refine Finset.sum_eq_zero fun x _ => ?_
          simp [A, AopM, hQ'.symm]
        · intro hQ; exact False.elim (hQ (Finset.mem_univ _))
      · intro ν' _ hν'
        refine Finset.sum_eq_zero fun Qx _ => ?_
        simp [A, AopM, hν'.symm]
      · intro hν; exact False.elim (hν (Finset.mem_univ _))
    rw [← hred, hentry]
    have heq : (⟨μ₁, ⟨ν, r₁, Q₀⟩, b₁⟩ : Σ μ : ΛG, AdBasM BH mult μ × Fin (mult l μ)) =
        ⟨μ₂, ⟨ν, r₂, Q₀⟩, b₂⟩ ↔ (⟨μ₁, r₁, b₁⟩ : MM mult l ν) = ⟨μ₂, r₂, b₂⟩ := by
      constructor
      · intro h
        obtain ⟨rfl, h2⟩ := Sigma.ext_iff.mp h
        obtain ⟨h3, rfl⟩ := Prod.ext_iff.mp (eq_of_heq h2)
        obtain ⟨_, h5⟩ := Sigma.ext_iff.mp h3
        obtain ⟨rfl, _⟩ := Prod.ext_iff.mp (eq_of_heq h5)
        rfl
      · intro h
        obtain ⟨rfl, h2⟩ := Sigma.ext_iff.mp h
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (eq_of_heq h2)
        rfl
    simp [heq]
  · ext x₁ x₂
    have hentry := congr_fun (congr_fun hA_unit.2 ⟨ν, Q₀, x₁⟩) ⟨ν, Q₀, x₂⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hentry ⊢
    let eOut : (Σ μ : ΛG, AdBasM BH mult μ × Fin (mult l μ)) ≃
        (Σ ν' : ΛH, BH ν' × MM mult l ν') :=
      { toFun := fun ⟨μ, ⟨ν', r, Q⟩, b⟩ => ⟨ν', Q, ⟨μ, r, b⟩⟩
        invFun := fun ⟨ν', Q, ⟨μ, r, b⟩⟩ => ⟨μ, ⟨ν', r, Q⟩, b⟩
        left_inv := fun ⟨_, ⟨_, _, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, ⟨_, _, _⟩⟩ => rfl }
    have hred :
        ∑ out : Σ μ : ΛG, AdBasM BH mult μ × Fin (mult l μ),
          star (A out ⟨ν, Q₀, x₁⟩) * A out ⟨ν, Q₀, x₂⟩ =
        ∑ mrb : MM mult l ν,
          star (AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν mrb x₁) *
            AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν mrb x₂ := by
      rw [Fintype.sum_equiv eOut
        (fun out => star (A out ⟨ν, Q₀, x₁⟩) * A out ⟨ν, Q₀, x₂⟩)
        (fun out' => star (A (eOut.symm out') ⟨ν, Q₀, x₁⟩) * A (eOut.symm out') ⟨ν, Q₀, x₂⟩)
        (fun _ => rfl)]
      rw [Fintype.sum_sigma, Finset.sum_eq_single ν]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single Q₀]
        · refine Finset.sum_congr rfl fun mrb _ => ?_
          simp [A, AopM, eOut]
        · intro Q' _ hQ'
          refine Finset.sum_eq_zero fun mrb _ => ?_
          simp [A, AopM, eOut, hQ']
        · intro hQ; exact False.elim (hQ (Finset.mem_univ _))
      · intro ν' _ hν'
        refine Finset.sum_eq_zero fun Qmrb _ => ?_
        simp [A, AopM, eOut, hν']
      · intro hν; exact False.elim (hν (Finset.mem_univ _))
    rw [← hred, hentry]
    have heq : (⟨ν, Q₀, x₁⟩ : NOutM Ω BH mL mE (Λω := Λω) l) = ⟨ν, Q₀, x₂⟩ ↔ x₁ = x₂ := by
      constructor
      · intro h
        exact congrArg Prod.snd (eq_of_heq (Sigma.ext_iff.mp h).2)
      · rintro rfl; rfl
    simp [heq]

end GL2QFT.Supplement.MackeyMultProof

open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.Mackey GL2QFT.Supplement.MackeyMult
  GL2QFT.Supplement.MackeyMultProof

theorem solution {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (mult : ΛH → ΛG → ℕ)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBasM BH mult μ) (AdBasM BH mult μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsAdaptedMult H BH mult RH RG)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type) [∀ ω κ, Fintype (Bω ω κ)]
    [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (mL : ∀ ω, ΛH → Λω ω → ℕ)
    (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
    (hL : ∀ ω ∈ Ω, ∀ ν, IsEmbeddingFamily H Bω (fun h => RH ν (h : H)) (mL ω ν) (Rω ω)
      (Lmat ω ν))
    (mE : ∀ ω, ΛH → Λω ω → ℕ)
    (Emat : ∀ ω l, Matrix (BH l) (Σ κ : Λω ω, Fin (mE ω l κ) × Bω ω κ) ℂ)
    (hE : ∀ ω ∈ Ω, ∀ l, IsEmbeddingFamily H Bω (twistRep H ω (RH l)) (mE ω l) (Rω ω) (Emat ω l))
    (l : ΛH) :
    AopM H Ω BH mult Bω RG mL Lmat mE Emat l * NopM H Ω Tω BH Bω RH mL Lmat mE Emat l =
        UIndMult H Ω Tω BH mult RG l ∧
      ∀ ν : ΛH,
        AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν *
            (AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν)ᴴ = 1 ∧
          (AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν)ᴴ *
            AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν = 1 :=
  ⟨aopM_mul_nopM H Ω hΩ Tω BH mult RH hRH RG hRG hAd Bω Rω hRω mL Lmat hL mE Emat hE l,
    fun ν => ablockM_isUnitary H Ω hΩ Tω hTω BH mult RH hRH RG hRG hAd Bω Rω hRω mL Lmat hL mE Emat hE l ν⟩
