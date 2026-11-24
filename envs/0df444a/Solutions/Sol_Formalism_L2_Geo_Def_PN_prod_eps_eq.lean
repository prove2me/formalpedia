-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PN.prod_eps_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:54:02.595967+00:00
-- url     : https://prove2.me/submissions/185a55f0-e14a-451d-8066-75302c85462b

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PNeatB
import Theorems.Thm_Formalism_UG_P_afsplitI_ne
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_levelaf_finite_places
import Theorems.Thm_Formalism_UG_P_levelaf_int_mem_v


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PN
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PN
theorem _root_.solution (d : 𝓞 F) (hd : d ≠ 0) :
    ∃ a ∈ intAd F, (∏ v ∈ (levelaf_finite_places d hd).toFinset, (1 - afsplitEps E v)) =
      ((1 : E) ⊗ₜ[F] a) * levelafC E d := by
  classical
  set T := (levelaf_finite_places d hd).toFinset with hT
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  refine ⟨algebraMap F 𝔸 (algebraMap (𝓞 F) F d)⁻¹ * ∏ v ∈ T, (1 - afsplitI v 1), ?_, ?_⟩
  · intro u
    have e : (algebraMap F 𝔸 (algebraMap (𝓞 F) F d)⁻¹ * ∏ v ∈ T, (1 - afsplitI v 1)) u =
        algebraMap F (u.adicCompletion F) (algebraMap (𝓞 F) F d)⁻¹ *
          ∏ v ∈ T, (1 - (afsplitI v (1 : v.adicCompletion F)) u) := by
      have := map_prod (evalV F u) (fun v => (1 - afsplitI v (1 : v.adicCompletion F))) T
      rw [afsplit_mul_apply]
      congr 1
    rw [e]
    by_cases hu : u ∈ T
    · rw [Finset.prod_eq_zero hu (by rw [afsplitI_self, sub_self]), mul_zero]
      exact zero_mem _
    · rw [Finset.prod_eq_one (fun v hv => by
        rw [afsplitI_ne v u (fun e => hu (e ▸ hv)), sub_zero]), mul_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
      have h1 : ¬ Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) d) < 1 := by
        simpa [hT] using hu
      have h2 : Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) d) ≤ 1 := levelaf_int_mem_v u d
      have h3 : Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) d) = 1 := le_antisymm h2 (not_lt.1 h1)
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (u.adicCompletion F)] at h3
      rw [h3, inv_one]
  · have e1 : ∀ v : HeightOneSpectrum (𝓞 F), (1 - afsplitEps E v) =
        (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) (1 - afsplitI v 1) := by
      intro v
      rw [map_sub, map_one]
      rfl
    rw [Finset.prod_congr rfl (fun v _ => e1 v), ← map_prod, levelafC,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.includeRight_apply]
    congr 1
    rw [mul_right_comm, IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸, ← map_mul, inv_mul_cancel₀ hdF, map_one,
      one_mul]
end Formalism.L2.Geo.Def.PN
