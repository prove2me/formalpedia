-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.linearCoeff_chordCoeffQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:13.973709+00:00
-- url     : https://prove2.me/submissions/5674c976-baa2-4aa7-89d8-f4cd0291b779

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_mul_vanishing_order_two
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_L
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_nu_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_nu_L
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace WeierstrassChordSeries
section Alg
variable {R : Type*} [CommRing R]
section maps
variable {R' : Type*} [CommRing R'] (φ : R →+* R')
end maps
section mem
variable (T : Subring R)
end mem
end Alg
section Fld
variable {F : Type*} [Field F]
end Fld
section Wser
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
variable {W}
end Wser
section Mser
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
private theorem cc_L_mul_eq_zero_of_vanishing {φ : MvPowerSeries (Fin 2) K} (h0 : cc φ = 0) (h1 : ∀ i, (L i) φ = 0)
    (ψ : MvPowerSeries (Fin 2) K) : cc (ψ * φ) = 0 ∧ ∀ i, (L i) (ψ * φ) = 0 := by
  rw [mul_comm]
  exact mul_vanishing_order_two h0 h1 ψ
end Mser
end WeierstrassChordSeries
end Formalism.ELL
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (hw : WFixed W w) (i : Fin 2) : (L i) (C2 W w) = 0 := by
  have hs0 := lam_cc hw
  have hs1 := lam_L hw
  have hn0 := nu_cc hw
  have hn1 := nu_L hw
  have hss := mul_vanishing_order_two hs0 hs1 (lam w)
  rw [C2, c2, pow_two]
  simp only [map_add, (cc_L_mul_eq_zero_of_vanishing hs0 hs1 _).2 i, (cc_L_mul_eq_zero_of_vanishing hn0 hn1 _).2 i,
    (cc_L_mul_eq_zero_of_vanishing hss.1 hss.2 _).2 i, add_zero]
end Formalism.ELL.WeierstrassChordSeries
