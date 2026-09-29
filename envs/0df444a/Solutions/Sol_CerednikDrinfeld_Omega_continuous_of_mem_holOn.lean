-- Prove2me | solution 1 for CerednikDrinfeld.Omega.continuous_of_mem_holOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5e403c74-1335-5f8a-bd22-19a4de19876b

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_continuous_of_mem_holOn

set_option autoImplicit false

p2m_open "Filter CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_continuous_of_mem_holOn.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.holOn"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "RatPair IsHolOn holOn"
namespace HolCont
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem continuous_evalAt {S : Set K} (r : RatPair K) (hr : r.IsPoleFreeOn S) :
    Continuous (fun z : ↥S => r.evalAt (z : K)) := by
  have hnum : Continuous (fun z : ↥S => r.num.eval (z : K)) := r.num.continuous.comp continuous_subtype_val
  have hden : Continuous (fun z : ↥S => r.den.eval (z : K)) := r.den.continuous.comp continuous_subtype_val
  exact hnum.div hden (fun z => hr z z.2)

theorem continuous_of_isHolOn {S : Set K} {g : ↥S → K} (hg : IsHolOn K S g) : Continuous g := by
  obtain ⟨r, hr, -, hlim⟩ := hg
  exact hlim.continuous (Frequently.of_forall fun k => continuous_evalAt (r k) (hr k))

end CerednikDrinfeld.Omega.HolCont

theorem solution (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S : Set K} {g : ↥S → K} (hg : g ∈ CerednikDrinfeld.Omega.holOn K S) : Continuous g :=
  CerednikDrinfeld.Omega.HolCont.continuous_of_isHolOn hg

end S_CerednikDrinfeld_Omega_continuous_of_mem_holOn
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_continuous_of_mem_holOn (solution)
