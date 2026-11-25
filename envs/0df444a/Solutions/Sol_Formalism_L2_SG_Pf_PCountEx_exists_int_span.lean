-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.exists_int_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:41.681999+00:00
-- url     : https://prove2.me/submissions/4419d715-ca1a-4511-be18-91ca95050ac0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SimpLemmas
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace Formalism.L2.SG.Pf.PCountEx
theorem _root_.solution : ∃ (n : ℕ) (e : Fin n → 𝓞 E), Submodule.span F (Set.range fun j => (e j : E)) = ⊤ := by
  let b := Module.finBasis F E
  have hm : ∀ i, ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * b i) := fun i => by
    have hx : IsAlgebraic ℤ (b i) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (b i))
    obtain ⟨k, hk0, hk⟩ := hx.exists_integral_multiple
    exact ⟨k, hk0, by simpa [zsmul_eq_mul, Algebra.smul_def] using hk⟩
  choose k hk0 hk using hm
  refine ⟨Module.finrank F E, fun i => ⟨(k i : E) * b i, hk i⟩, ?_⟩
  rw [eq_top_iff]
  intro x _
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e1 : b.repr x i • b i = (b.repr x i * ((k i : F))⁻¹) • ((k i : E) * b i) := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀, map_intCast]
    have hk' : ((k i : ℤ) : E) ≠ 0 := by exact_mod_cast hk0 i
    field_simp
  rw [e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.L2.SG.Pf.PCountEx
