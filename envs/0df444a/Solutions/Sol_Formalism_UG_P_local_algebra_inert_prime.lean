-- Prove2me | solution 1 for Formalism.UG.P.local_algebra_inert_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:32.507587+00:00
-- url     : https://prove2.me/submissions/b5710693-c9d8-4a91-b10d-c8a7b3d5a38f

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
import Theorems.Thm_Formalism_UG_P_gLoc_main
import Theorems.Thm_Formalism_UG_P_stabilizer_standard_lattice


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
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.LocInert := by
  intro F E _ _ _ _ _ σ n v L _ _ _ e σw P he hT hPO hP
  have hH : ∀ g, g ∈ UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ↔
      g ∈ UJ (sigR σ (v.adicCompletion F)) (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
    intro g
    rw [UPts, Matrix.map_one _ (map_zero _) (map_one _)]
  have hLv : ∀ g, g ∈ levelV σ (1 : Matrix (Fin n) (Fin n) E) v ↔
      g ∈ UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ∧
      g ∈ (bc (n := Fin n) (tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v)).subtype).range := by
    intro g
    rw [levelV, level, Subgroup.mem_inf,
      stabilizer_standard_lattice _ _ (Fin n) (fun a b h => Subtype.ext h)]
    rfl
  obtain ⟨f, hf1, hf2⟩ := gLoc_main (sigR σ (v.adicCompletion F)) σw e he _ hT P hPO hP _ _ hH hLv
  exact ⟨f, hf1, hf2⟩
end Formalism.UG.P
