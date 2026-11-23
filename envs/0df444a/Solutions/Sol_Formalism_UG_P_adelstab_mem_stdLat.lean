-- Prove2me | solution 1 for Formalism.UG.P.adelstab_mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:37.491854+00:00
-- url     : https://prove2.me/submissions/d9cf2f9b-1b61-4a84-8286-98a3767464bb

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab

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
theorem _root_.solution (v : n → 𝒜) : v ∈ stdLat (n := n) (A := 𝒜) ↥𝒮 ↔ ∀ i, v i ∈ 𝒮 := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨v i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2
end Formalism.UG.P
