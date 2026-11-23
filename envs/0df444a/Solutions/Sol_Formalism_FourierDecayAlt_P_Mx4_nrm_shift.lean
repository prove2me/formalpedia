-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.nrm_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:27.585982+00:00
-- url     : https://prove2.me/submissions/d9f0507d-5b07-4b40-8743-cd275d750c8d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_rhoUp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πj : Ty P) (hU : Up P j π πj) (hp : rho P π j - rho P π l + 1 ≠ 0) (hm : rho P π j - rho P π l - 1 ≠ 0) :
    Nrm P l πj * (rho P π j - rho P π l + 1) = Nrm P l π * (rho P π j - rho P π l - 1) := by
  have hr := rhoUp P j π πj hU
  have hrl : rho P πj l = rho P π l := by rw [hr l hl, if_neg hjl.symm, add_zero]
  have hrj : rho P πj j = rho P π j + 1 := by rw [hr j hj, if_pos rfl]
  have hjm : j ∈ (Icc 1 (P.k - 1)).erase l := Finset.mem_erase.2 ⟨hjl, hj⟩
  have hother : ∀ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, rho P πj i = rho P π i := by
    intro i hi
    have h1 := Finset.mem_erase.1 hi
    rw [hr i (Finset.mem_of_mem_erase h1.2), if_neg h1.1, add_zero]
  have p1 : ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (rho P πj i - rho P πj l) =
      (rho P π j - rho P π l + 1) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (rho P π i - rho P π l) := by
    rw [← Finset.mul_prod_erase _ _ hjm, hrj, hrl]
    congr 1
    · ring
    · exact Finset.prod_congr rfl (fun i hi => by rw [hother i hi])
  have p2 : ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (rho P πj i - rho P πj l - 1) =
      (rho P π j - rho P π l) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (rho P π i - rho P π l - 1) := by
    rw [← Finset.mul_prod_erase _ _ hjm, hrj, hrl]
    congr 1
    · ring
    · exact Finset.prod_congr rfl (fun i hi => by rw [hother i hi])
  have p3 : ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (rho P π i - rho P π l) =
      (rho P π j - rho P π l) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (rho P π i - rho P π l) :=
    (Finset.mul_prod_erase _ _ hjm).symm
  have p4 : ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (rho P π i - rho P π l - 1) =
      (rho P π j - rho P π l - 1) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (rho P π i - rho P π l - 1) :=
    (Finset.mul_prod_erase _ _ hjm).symm
  have g : ∀ Q A B d : ℝ, d + 1 ≠ 0 → d - 1 ≠ 0 →
      Q / (((d + 1) * A) * (d * B)) * (d + 1) = Q / ((d * A) * ((d - 1) * B)) * (d - 1) := by
    intro Q A B d hp hm
    have e1 : ((d + 1) * A) * (d * B) = (d + 1) * (A * d * B) := by ring
    have e2 : (d * A) * ((d - 1) * B) = (d - 1) * (A * d * B) := by ring
    rw [e1, e2, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm Q (d + 1), mul_comm Q (d - 1),
      mul_div_mul_left _ _ hp, mul_div_mul_left _ _ hm]
  unfold Nrm
  rw [p1, p2, p3, p4, hrl]
  exact g _ _ _ _ hp hm
end Formalism.FourierDecayAlt.P.Mx4
