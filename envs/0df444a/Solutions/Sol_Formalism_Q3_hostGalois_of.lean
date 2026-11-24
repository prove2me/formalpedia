-- Prove2me | solution 1 for Formalism.Q3.hostGalois_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:08.645907+00:00
-- url     : https://prove2.me/submissions/70080727-b8bf-410d-9251-874669202e3e

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer
import Theorems.Thm_Formalism_Q3_host_not_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (hG : MQGalois) (hK : MQKummer) : HostGalois := by
  unfold MQGalois at hG
  unfold MQKummer at hK
  unfold HostGalois
  intro q hq E _ _ α hα
  have hα' : IsMQ (fun i => -(q i : ℤ)) α := hα
  have hne : ∀ i, (fun i => -(q i : ℤ)) i ≠ 0 := by
    intro i
    have := (hq.1 i).1.pos
    show -(q i : ℤ) ≠ 0
    omega
  obtain ⟨hgal, -, hmul, -⟩ := hG 3 E (fun i => -(q i : ℤ)) α hα' hne
  obtain ⟨hfr, hbij, -⟩ := hK 3 E (fun i => -(q i : ℤ)) α hα' (fun S hS => host_not_sq q hq S hS)
  exact ⟨hgal, by rw [hfr]; norm_num, hbij, hmul⟩
end Formalism.Q3
