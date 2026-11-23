-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:01.912282+00:00
-- url     : https://prove2.me/submissions/be1c00ea-6790-4f5e-ae4a-fabafa11fe9f

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution [T2Space K] (R : Subring K) (hR : IsCompact (R : Set K)) (n : ℕ) :
    IsCompact (glR R n : Set (GL (Fin n) K)) := by
  let S : Set (Matrix (Fin n) (Fin n) K) :=
    Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (R : Set K)))
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hR))
  have hS' : IsCompact (MulOpposite.unop ⁻¹' S : Set (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.isCompact_preimage.mp hS
  have := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  convert this using 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a _ b _ => h1 a b, fun a _ b _ => h2 a b⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b => h1 a (Set.mem_univ _) b (Set.mem_univ _),
      fun a b => h2 a (Set.mem_univ _) b (Set.mem_univ _)⟩
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
