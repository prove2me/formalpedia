-- Prove2me | solution 1 for BaconThesis.Control.eq_3_9
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T23:05:10.171815+00:00
-- url     : https://prove2.me/submissions/91c5b955-6ae4-4182-a3fb-8798d297ee08

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_IsFixedBasis
import Definitions.Def_BaconThesis_Control_coeffOp
import Definitions.Def_BaconThesis_Control_HA

open scoped Matrix Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace BaconThesis.Control.SolM3_9

open BaconThesis.Control

section spanning

variable {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

private lemma linear_eq_zero_of_single (L : Matrix n n ℂ →ₗ[ℂ] V)
    (h : ∀ i j, L (Matrix.single i j 1) = 0) (X : Matrix n n ℂ) : L X = 0 := by
  rw [Matrix.matrix_eq_sum_single X, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, h, smul_zero]

private lemma exists_normalize (w : n → ℂ) (hw : w ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ star (a • w) ⬝ᵥ (a • w) = 1 := by
  have hx : star w ⬝ᵥ w ≠ 0 := mt dotProduct_star_self_eq_zero.mp hw
  have hnn : 0 ≤ star w ⬝ᵥ w := dotProduct_star_self_nonneg w
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnn
  set r : ℝ := (star w ⬝ᵥ w).re with hr
  have hxr : star w ⬝ᵥ w = (r : ℂ) := Complex.ext rfl (by simpa using him.symm)
  have hrpos : 0 < r := lt_of_le_of_ne hre fun h => hx (by rw [hxr, ← h]; simp)
  have hs : (Real.sqrt r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hrpos).ne'
  refine ⟨(Real.sqrt r : ℂ)⁻¹, inv_ne_zero hs, ?_⟩
  rw [star_smul, smul_dotProduct, dotProduct_smul, hxr, smul_eq_mul, smul_eq_mul]
  have h2 : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hrpos.le
  have hstar : star ((Real.sqrt r : ℂ)⁻¹) = (Real.sqrt r : ℂ)⁻¹ := by simp
  rw [hstar, ← h2]
  field_simp

/-- A linear functional that vanishes on every density operator is zero. -/
private lemma functional_eq_zero_of_density (L : Matrix n n ℂ →ₗ[ℂ] ℂ)
    (h : ∀ ρ, WildeQIT.IsDensityOperator ρ → L ρ = 0) (X : Matrix n n ℂ) : L X = 0 := by
  have hq : ∀ v : n → ℂ, L (Matrix.vecMulVec v (star v)) = 0 := by
    intro v
    by_cases hv : v = 0
    · subst hv
      have : Matrix.vecMulVec (0 : n → ℂ) (star (0 : n → ℂ)) = 0 := by ext; simp [Matrix.vecMulVec_apply]
      rw [this, map_zero]
    obtain ⟨a, ha, hav⟩ := exists_normalize v hv
    have hρ : WildeQIT.IsDensityOperator (Matrix.vecMulVec (a • v) (star (a • v))) :=
      ⟨Matrix.posSemidef_vecMulVec_self_star _, by
        rw [Matrix.trace_vecMulVec, dotProduct_comm]; exact hav⟩
    have h1 := h _ hρ
    rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, map_smul, map_smul] at h1
    exact (smul_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left ha)).resolve_left
      (star_ne_zero.mpr ha)
  have hB : ∀ u v : n → ℂ, L (Matrix.vecMulVec u (star v)) = 0 := by
    intro u v
    have h1 := hq (u + v)
    have h2 := hq (u + Complex.I • v)
    simp only [star_add, star_smul, Matrix.add_vecMulVec, Matrix.vecMulVec_add,
      Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, map_add, map_smul, hq u, hq v,
      Complex.star_def, Complex.conj_I] at h1 h2
    simp only [smul_eq_mul] at h1 h2
    linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2 : ℂ) * h2 +
      ((L (Matrix.vecMulVec u (star v)) - L (Matrix.vecMulVec v (star u))) / 2) * Complex.I_sq
  refine linear_eq_zero_of_single L (fun i j => ?_) X
  have := hB (Pi.single i 1) (Pi.single j 1)
  rwa [Matrix.single_eq_single_vecMulVec_single, show (Pi.single j (1 : ℂ) : n → ℂ) =
    star (Pi.single j (1 : ℂ) : n → ℂ) from by ext k; simp [Pi.single_apply, apply_ite]]

/-- A matrix-valued linear map that vanishes on every density operator is zero. -/
private lemma linear_eq_zero_of_density {m : Type} (L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : ∀ ρ, WildeQIT.IsDensityOperator ρ → L ρ = 0) (X : Matrix n n ℂ) : L X = 0 := by
  ext i j
  exact functional_eq_zero_of_density ((Matrix.entryLinearMap ℂ ℂ i j).comp L)
    (fun ρ hρ => by simp [h ρ hρ]) X

end spanning

end BaconThesis.Control.SolM3_9

open BaconThesis.Control BaconThesis.Control.SolM3_9 in
theorem solution {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    [Fintype κ] [DecidableEq κ]
    (H : Matrix (s × a) (s × a) ℂ) (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (v : a → ℂ)
    (h38 : ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
      ∑ α ∈ Finset.univ.erase i0, (F α * ρ).trace •
          (coeffOp H F α * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * coeffOp H F α) +
        (HA H * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * HA H) = 0) :
    (∀ α, α ≠ i0 →
      coeffOp H F α * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * coeffOp H F α = 0) ∧
    HA H * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * HA H = 0 := by
  obtain ⟨hherm, -, htr0, horth, -⟩ := hF
  set C : κ → Matrix a a ℂ := fun α =>
    coeffOp H F α * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * coeffOp H F α
    with hC
  set C0 := HA H * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * HA H with hC0
  have ht : ∀ α β, (F α * F β).trace = if α = β then 1 else 0 := by
    intro α β
    have := horth α β
    rwa [(hherm α).eq] at this
  have hne : Nonempty s := by
    rcases isEmpty_or_nonempty s with h | h
    · have := horth i0 i0
      simp [Matrix.trace] at this
    · exact h
  have hcard : (Fintype.card s : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- the maximally mixed state kills the first sum
  set ρ0 : Matrix s s ℂ := ((Fintype.card s : ℝ)⁻¹ : ℝ) • (1 : Matrix s s ℂ) with hρ0
  have hρ0d : WildeQIT.IsDensityOperator ρ0 := by
    refine ⟨Matrix.PosSemidef.one.smul (by positivity), ?_⟩
    rw [hρ0, Matrix.trace_smul, Matrix.trace_one]
    simp [hcard]
  have hC0z : C0 = 0 := by
    have := h38 ρ0 hρ0d
    rw [Finset.sum_eq_zero, zero_add] at this
    · exact this
    intro α hα
    rw [hρ0, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
      htr0 α (Finset.ne_of_mem_erase hα), smul_zero, zero_smul]
  refine ⟨fun β hβ => ?_, hC0z⟩
  let L : Matrix s s ℂ →ₗ[ℂ] Matrix a a ℂ :=
    { toFun := fun X => ∑ α ∈ Finset.univ.erase i0, (F α * X).trace • C α
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c X => by
        simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum,
          RingHom.id_apply] }
  have hL : ∀ ρ, WildeQIT.IsDensityOperator ρ → L ρ = 0 := by
    intro ρ hρ
    have := h38 ρ hρ
    rw [hC0z, add_zero] at this
    exact this
  have h1 := linear_eq_zero_of_density L hL (F β)
  change ∑ α ∈ Finset.univ.erase i0, (F α * F β).trace • C α = 0 at h1
  simp only [ht] at h1
  rw [Finset.sum_eq_single β] at h1
  · simpa using h1
  · intro α _ hαβ
    simp [hαβ]
  · intro hβ'
    exact absurd (Finset.mem_erase.mpr ⟨hβ, Finset.mem_univ β⟩) hβ'
