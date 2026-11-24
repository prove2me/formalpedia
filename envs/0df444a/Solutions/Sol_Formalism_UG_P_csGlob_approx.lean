-- Prove2me | solution 1 for Formalism.UG.P.csGlob_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:22:33.524394+00:00
-- url     : https://prove2.me/submissions/b883a242-a50c-4ec3-b538-e01018befe2b

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Theorems.Thm_Formalism_UG_P_csGlob_tmul_int
import Theorems.Thm_Formalism_UG_P_levelaf_decomp
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (hA : Formalism.UG.CS.IntAdApprox) (D : 𝓞 F) (hD : D ≠ 0) (s : 𝒜)
    (hs : s ∈ 𝒮) : ∃ b : 𝓞 E, ∃ t ∈ 𝒮, s = ι (algebraMap (𝓞 E) E b) + levelafC E D * t := by
  classical
  obtain ⟨m, bb, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨r, hr, rfl⟩ := levelaf_decomp bb hb hs
  choose ρ y hy hρ using fun j => hA F D hD (r j) (hr j)
  refine ⟨∑ j, algebraMap (𝓞 F) (𝓞 E) (ρ j) * bb j, ∑ j, algebraMap (𝓞 E) E (bb j) ⊗ₜ[F] y j,
    sum_mem fun j _ => levelaf_tmul_mem _ (hy j), ?_⟩
  simp only [hρ, TensorProduct.tmul_add, Finset.sum_add_distrib, map_sum, Finset.mul_sum, levelafC,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [csGlob_tmul_int, map_mul (algebraMap (𝓞 E) E), ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E,
    map_mul]
end Formalism.UG.P
