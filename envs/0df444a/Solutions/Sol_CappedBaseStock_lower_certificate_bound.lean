-- Prove2me | solution 1 for CappedBaseStock.lower_certificate_bound
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:25:23.220309+00:00
-- url     : https://prove2.me/submissions/321d928c-b874-453e-b92a-fec3acddef22

import Theorems.Thm_CappedBaseStock_policy_window_relaxation
import Theorems.Thm_CappedBaseStock_window_jensen_certificate

open CappedBaseStock
open scoped ENNReal NNReal

/-- Finite-policy window relaxation and the two Jensen inequalities give a
certificate arbitrarily close to each finite policy cost. Infima and an
extended-nonnegative epsilon argument finish without an optimal policy. -/
theorem solution (P : DemandLaw) (c : Parameters) :
    lowerCertificate P c ≤ OPT P c := by
  unfold OPT
  apply le_iInf
  intro π
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  rcases policy_window_relaxation P c π hfinite ε (by exact_mod_cast hε) with
    ⟨W, r, z, hr, hrmean, hz, hmeans, hL, hL1, hobj⟩
  have hfeas : CertificateFeasible P c r z := by
    refine ⟨hr, hrmean, hz, ?_, ?_⟩
    · exact window_jensen_certificate P (c.L + 1) W r z hr hrmean hz hmeans
        c.L c.leadTime_pos (Nat.le_succ c.L) hL
    · simpa only [Nat.cast_add, Nat.cast_one] using
        window_jensen_certificate P (c.L + 1) W r z hr hrmean hz hmeans
          (c.L + 1) (Nat.succ_pos c.L) le_rfl hL1
  have hle : lowerCertificate P c ≤ certificateObjective P c r z :=
    iInf_le (fun rz : {rz : ℝ × ℝ // CertificateFeasible P c rz.1 rz.2} =>
      certificateObjective P c rz.val.1 rz.val.2) ⟨(r, z), hfeas⟩
  exact hle.trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hobj)
