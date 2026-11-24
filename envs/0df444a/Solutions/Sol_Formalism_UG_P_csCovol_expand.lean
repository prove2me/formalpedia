-- Prove2me | solution 1 for Formalism.UG.P.csCovol_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:11.315891+00:00
-- url     : https://prove2.me/submissions/b343037f-2d9f-4454-ac5f-8b77b2e4a55f

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol
import Theorems.Thm_Formalism_UG_P_csCovol_mem_zmap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {N : ℕ}
  (ι : V →+ EuclideanSpace ℝ (Fin N))
namespace Formalism.UG.P
theorem _root_.solution
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) (b : Basis (Fin N) ℤ (Formalism.HermitianLatticesTheory.zmap ι M)) (m : Fin N → V)
    (hm : ∀ i, ι (m i) = b i) (z : V) (hz : z ∈ M) :
    ∃ a : Fin N → ℤ, (∀ w : V, Algebra.trace ℚ K (h w z) =
        ∑ j, (a j : ℚ) * Algebra.trace ℚ K (h w (m j))) ∧
      (∀ w : V, Algebra.trace ℚ K (h z w) = ∑ j, (a j : ℚ) * Algebra.trace ℚ K (h (m j) w)) := by
  have hz' : ι z ∈ Formalism.HermitianLatticesTheory.zmap ι M := (csCovol_mem_zmap ι M (ι z)).mpr ⟨z, hz, rfl⟩
  have h1 : (⟨ι z, hz'⟩ : Formalism.HermitianLatticesTheory.zmap ι M) = ∑ j, b.repr ⟨ι z, hz'⟩ j • b j := (b.sum_repr _).symm
  have h2 := congrArg Subtype.val h1
  simp only [Submodule.coe_sum, SetLike.val_smul, ← hm] at h2
  refine ⟨fun j => b.repr ⟨ι z, hz'⟩ j, fun w => ?_, fun w => ?_⟩
  · have e1 := hι w z
    rw [h2, inner_sum] at e1
    simp only [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hι] at e1
    have e2 : ((Algebra.trace ℚ K (h w z) : ℚ) : ℝ) =
        ((∑ j, ((b.repr ⟨ι z, hz'⟩ j : ℤ) : ℚ) * Algebra.trace ℚ K (h w (m j)) : ℚ) : ℝ) := by
      push_cast
      first | exact e1 | exact e1.symm
    exact_mod_cast e2
  · have e1 := hι z w
    rw [h2, sum_inner] at e1
    simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hι] at e1
    have e2 : ((Algebra.trace ℚ K (h z w) : ℚ) : ℝ) =
        ((∑ j, ((b.repr ⟨ι z, hz'⟩ j : ℤ) : ℚ) * Algebra.trace ℚ K (h (m j) w) : ℚ) : ℝ) := by
      push_cast
      first | exact e1 | exact e1.symm
    exact_mod_cast e2
end Formalism.UG.P
