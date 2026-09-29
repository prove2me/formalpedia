-- Prove2me | solution 1 for Erdos9796FiniteNine.cap_containment
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T06:49:05.81592+00:00
-- url     : https://prove2.me/submissions/2ab7afe0-25de-4ecb-b326-1bcb63a31b23

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Erdos9796FiniteNine_N4dPackets
import Definitions.Def_Erdos9796FiniteNine_N4dFormBBranchSupport
import Theorems.Thm_Erdos9796FiniteNine_n4e_core
import Theorems.Thm_Erdos9796FiniteNine_n4d_formb_branch
import Theorems.Thm_Erdos9796FiniteNine_form_a_v1
import Theorems.Thm_Erdos9796FiniteNine_form_b_v1
import Theorems.Thm_Erdos9796FiniteNine_form_b_v2
import Theorems.Thm_Erdos9796FiniteNine_form_c_v1
import Theorems.Thm_Erdos9796FiniteNine_cyclic_forms


section Batch3N9Unit051CapContainment
namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
namespace FiniteEndpointShell

private noncomputable def p2mCoreSupport {A : Finset ℝ²}
    (S : FiniteEndpointShell A) : N4eCoreSupport S :=
  Classical.choice (Erdos9796FiniteNine.n4e_core S)

private noncomputable def p2mBranchSupport {A : Finset ℝ²}
    (S : FiniteEndpointShell A) (Z : ZeroDefectCapLayout S) :
    N4dFormBBranchSupport S Z :=
  Classical.choice (Erdos9796FiniteNine.n4d_formb_branch S Z)

set_option maxHeartbeats 2000000 in
theorem selectorShape_v2_q_eq_v1_forces_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hr : 0 < r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s) :
    S.witnessClassAt_v2 s ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) := by
  classical
  rcases hbranch with ⟨⟨hA2, h_a2eq, h_v2eq⟩, -, hpacket⟩
  rcases hpacket with ⟨hTcard_packet, hI2sub_packet, p, hp, hpeq, hqeq⟩
  have hforce : S.SharedCirclePointForcesV3 Z r s := by
    intro q hqnamed hqT2 hqT1
    let q1 : ℝ² := S.triangle.v1
    let q2 : ℝ² := S.triangle.v2
    let a : ℝ² := Z.a2
    let center : ℝ² := S.Packet.center
    have hqA : q ∈ A := (Finset.mem_filter.mp hqT1).1
    have haC2 : a ∈ S.CP.C2 := by
      unfold Problem97.FiniteEndpointShell.I2 at hA2
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).2
    have haA : a ∈ A := S.CP.C2_subset haC2
    have haT1 : a ∈ S.witnessClassAt_v1 r := by
      have hamem : a ∈ ({a} : Finset ℝ²) := by simp
      rw [← h_a2eq] at hamem
      exact (Finset.mem_inter.mp hamem).1
    have haT2 : a ∈ S.witnessClassAt_v2 s := by
      exact hI2sub_packet hA2
    have hv2T1 : q2 ∈ S.witnessClassAt_v1 r := by
      have hv2mem : q2 ∈ ({q2} : Finset ℝ²) := by simp [q2]
      rw [← h_v2eq] at hv2mem
      exact (Finset.mem_inter.mp hv2mem).1
    have hv1T2 : q1 ∈ S.witnessClassAt_v2 s := by
      have hv1mem : q1 ∈ ({q1} : Finset ℝ²) := by simp [q1]
      rw [← hqeq] at hv1mem
      exact (Finset.mem_inter.mp hv1mem).1
    have hr_q1q2 : dist q1 q2 = r := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv2T1).2
    have hr_q1a : dist q1 a = r := by
      simpa [q1, a] using (Finset.mem_filter.mp haT1).2
    have hr_q1q : dist q1 q = r := by
      simpa [q1] using (Finset.mem_filter.mp hqT1).2
    have hs_q2q1 : dist q2 q1 = s := by
      simpa [q1, q2] using (Finset.mem_filter.mp hv1T2).2
    have hs_q2a : dist q2 a = s := by
      simpa [q2, a] using (Finset.mem_filter.mp haT2).2
    have hs_q2q : dist q2 q = s := by
      simpa [q2] using (Finset.mem_filter.mp hqT2).2
    have ha_q1 : dist q1 a = dist q1 q2 := by
      rw [hr_q1a, hr_q1q2]
    have ha_q2 : dist q2 a = dist q1 q2 := by
      rw [hs_q2a, dist_comm q1 q2, hs_q2q1]
    have hq_q1 : dist q1 q = dist q1 q2 := by
      rw [hr_q1q, hr_q1q2]
    have hq_q2 : dist q2 q = dist q1 q2 := by
      rw [hs_q2q, dist_comm q1 q2, hs_q2q1]
    have hu : q2 - q1 ≠ 0 := by
      exact sub_ne_zero.mpr S.triangle.v12_ne.symm
    let u : ℝ² := q2 - q1
    let nvec : ℝ² := Problem97.stdOrientation.rightAngleRotation u
    let β := Problem97.stdOrientation.basisRightAngleRotation u hu
    let M : ℝ² := midpoint ℝ q1 q2
    let X : ℝ² → ℝ := fun z => β.repr (z - M) 0
    let Y : ℝ² → ℝ := fun z => β.repr (z - M) 1
    let yc : ℝ := Y center
    have hsum_pt : ∀ z : ℝ², z - M = X z • u + Y z • nvec := by
      intro z
      simpa [β, X, Y, nvec] using (β.sum_repr (z - M)).symm
    have hnorm_nvec : ‖nvec‖ = ‖u‖ := by
      simpa [nvec] using Problem97.stdOrientation.rightAngleRotation.norm_map u
    have hβu : β.repr u = Finsupp.single 0 (1 : ℝ) := by
      simpa [β, nvec] using (β.repr_self 0)
    have hβu0 : β.repr u 0 = 1 := by simp [hβu]
    have horth : inner ℝ u nvec = 0 := by
      simpa [nvec] using Problem97.stdOrientation.inner_rightAngleRotation_self u
    have hq1mid : q1 - M = (-(1 / 2 : ℝ)) • u := by
      calc
        q1 - M = (1 / 2 : ℝ) • (q1 - q2) := by
          simpa [M] using (left_sub_midpoint ℝ q1 q2)
        _ = (-(1 / 2 : ℝ)) • u := by
          rw [show q1 - q2 = -u by
            dsimp [u]
            abel_nf]
          simp [smul_neg]
    have hq2mid : q2 - M = (1 / 2 : ℝ) • u := by
      simpa [M, u] using (right_sub_midpoint ℝ q1 q2)
    have hX_q1 : X q1 = -(1 / 2 : ℝ) := by
      have h := congrArg (fun v : ℝ² => β.repr v 0) hq1mid
      change X q1 = (β.repr ((-(1 / 2 : ℝ)) • u)) 0 at h
      rw [map_smul, hβu] at h
      simpa using h
    have hY_q1 : Y q1 = 0 := by
      have h := congrArg (fun v : ℝ² => β.repr v 1) hq1mid
      change Y q1 = (β.repr ((-(1 / 2 : ℝ)) • u)) 1 at h
      rw [map_smul, hβu] at h
      simpa using h
    have hX_q2 : X q2 = (1 / 2 : ℝ) := by
      have h := congrArg (fun v : ℝ² => β.repr v 0) hq2mid
      change X q2 = (β.repr ((1 / 2 : ℝ) • u)) 0 at h
      rw [map_smul, hβu] at h
      simpa using h
    have hY_q2 : Y q2 = 0 := by
      have h := congrArg (fun v : ℝ² => β.repr v 1) hq2mid
      change Y q2 = (β.repr ((1 / 2 : ℝ) • u)) 1 at h
      rw [map_smul, hβu] at h
      simpa using h
    have hdist_sq_coeff :
        ∀ a b : ℝ, ‖a • u + b • nvec‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u‖ ^ 2 := by
      intro a b
      have horth' : inner ℝ (a • u) (b • nvec) = 0 := by
        rw [inner_smul_left, inner_smul_right, horth]
        ring
      have hnorm :
          ‖a • u + b • nvec‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • nvec‖ ^ 2 := by
        simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • u) (b • nvec) horth'
      have hu_part : ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
        calc
          ‖a • u‖ ^ 2 = (|a| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
          _ = |a| ^ 2 * ‖u‖ ^ 2 := by ring
          _ = a ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
      have hn_part : ‖b • nvec‖ ^ 2 = b ^ 2 * ‖u‖ ^ 2 := by
        calc
          ‖b • nvec‖ ^ 2 = (|b| * ‖u‖) ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs, hnorm_nvec]
          _ = |b| ^ 2 * ‖u‖ ^ 2 := by ring
          _ = b ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
      rw [hnorm, hu_part, hn_part]
      ring
    have hpt_minus_q1 : ∀ z : ℝ²,
        z - q1 = (X z + 1 / 2) • u + Y z • nvec := by
      intro z
      calc
        z - q1 = (z - M) - (q1 - M) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
          abel_nf
        _ = (X z • u + Y z • nvec) - ((-(1 / 2 : ℝ)) • u) := by
          rw [hsum_pt z, hq1mid]
        _ = (X z • u + (1 / 2 : ℝ) • u) + Y z • nvec := by
          rw [sub_eq_add_neg, neg_smul]
          abel_nf
        _ = (X z + 1 / 2) • u + Y z • nvec := by
          rw [← add_smul]
    have hpt_minus_q2 : ∀ z : ℝ²,
        z - q2 = (X z - 1 / 2) • u + Y z • nvec := by
      intro z
      calc
        z - q2 = (z - M) - (q2 - M) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
          abel_nf
        _ = (X z • u + Y z • nvec) - ((1 / 2 : ℝ) • u) := by
          rw [hsum_pt z, hq2mid]
        _ = (X z • u + (-(1 / 2 : ℝ)) • u) + Y z • nvec := by
          rw [sub_eq_add_neg, neg_smul]
          abel_nf
        _ = (X z - 1 / 2) • u + Y z • nvec := by
          rw [← add_smul]
          simp [sub_eq_add_neg]
    have hpt_minus_center : ∀ z : ℝ²,
        z - center = X z • u + (Y z - yc) • nvec := by
      intro z
      have hcenter_perp : inner ℝ (center - M) u = 0 := by
        have hdist_eq : dist center q1 = dist center q2 := by
          rw [dist_comm center q1, dist_comm center q2, dist_eq_norm, dist_eq_norm]
          exact S.Packet.moser_on_boundary_1.trans S.Packet.moser_on_boundary_2.symm
        have hperp : center ∈ AffineSubspace.perpBisector q1 q2 := by
          rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
          simpa using hdist_eq
        have h :=
          (AffineSubspace.mem_perpBisector_iff_inner_eq_zero
            (c := center) (p₁ := q1) (p₂ := q2)).mp hperp
        simpa [M] using h
      have hxc_zero : X center = 0 := by
        have hinner : inner ℝ (center - M) u = X center * ‖u‖ ^ 2 := by
          have horth_rev : inner ℝ nvec u = 0 := by simpa [real_inner_comm] using horth
          calc
            inner ℝ (center - M) u = inner ℝ (X center • u + Y center • nvec) u := by
              rw [hsum_pt center]
            _ = inner ℝ (X center • u) u + inner ℝ (Y center • nvec) u := by
              rw [inner_add_left]
            _ = X center * ‖u‖ ^ 2 + Y center * 0 := by
              rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, horth_rev]
              simp
            _ = X center * ‖u‖ ^ 2 := by ring
        have hsqpos : 0 < ‖u‖ ^ 2 := by
          exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
        nlinarith only [hcenter_perp, hinner, hsqpos]
      calc
        z - center = (z - M) - (center - M) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
          abel_nf
        _ = (X z • u + Y z • nvec) - (Y center • nvec) := by
          rw [hsum_pt z, hsum_pt center, hxc_zero, zero_smul, zero_add]
        _ = X z • u + (Y z • nvec + (-Y center) • nvec) := by
          rw [sub_eq_add_neg, neg_smul]
          abel_nf
        _ = X z • u + (Y z - yc) • nvec := by
          rw [← add_smul]
          rfl
    have hdist_q1_sq :
        ∀ z : ℝ², dist q1 z ^ 2 = ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_q1, hdist_sq_coeff]
    have hdist_q2_sq :
        ∀ z : ℝ², dist q2 z ^ 2 = ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_q2, hdist_sq_coeff]
    have hdist_center_sq :
        ∀ z : ℝ², dist center z ^ 2 = (X z ^ 2 + (Y z - yc) ^ 2) * ‖u‖ ^ 2 := by
      intro z
      rw [dist_comm, dist_eq_norm, hpt_minus_center, hdist_sq_coeff]
    have hu_sq_pos : 0 < ‖u‖ ^ 2 := by
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
    have hcommon_coords :
        ∀ z : ℝ²,
          dist q1 z = dist q1 q2 →
          dist q2 z = dist q1 q2 →
          X z = 0 ∧ Y z ^ 2 = (3 : ℝ) / 4 := by
      intro z hz1 hz2
      have h1 : ((X z + 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 := by
        rw [← hdist_q1_sq z, hz1, dist_eq_norm]
        simpa [u, norm_sub_rev]
      have h2 : ((X z - 1 / 2) ^ 2 + Y z ^ 2) * ‖u‖ ^ 2 = ‖u‖ ^ 2 := by
        rw [← hdist_q2_sq z, hz2, dist_eq_norm]
        simpa [u, norm_sub_rev]
      have hx : X z = 0 := by
        nlinarith only [h1, h2, hu_sq_pos]
      have hy : Y z ^ 2 = (3 : ℝ) / 4 := by
        nlinarith only [h1, h2, hu_sq_pos, hx]
      exact ⟨hx, hy⟩
    have haXhY := hcommon_coords a ha_q1 ha_q2
    have hqXhY := hcommon_coords q hq_q1 hq_q2
    rcases haXhY with ⟨haX, haYsq⟩
    rcases hqXhY with ⟨hqX, hqYsq⟩
    have hy_cases : Y q = Y a ∨ Y q = -Y a := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      rw [hqYsq, haYsq]
    rcases Finset.mem_insert.mp hqnamed with hqa1 | hqrest
    · have hq_a1 : q = Z.a1 := by simpa using hqa1
      rcases hy_cases with hsame | hopp
      · have hqa2 : q = a := by
          have hsub : q - M = a - M := by
            calc
              q - M = X q • u + Y q • nvec := by rw [hsum_pt q]
              _ = 0 • u + Y a • nvec := by simpa [hqX, hsame]
              _ = X a • u + Y a • nvec := by simpa [haX]
              _ = a - M := by rw [hsum_pt a]
          have hadd := congrArg (fun t : ℝ² => t + M) hsub
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
        have hqI1 : q ∈ S.I1 := by
          rw [hq_a1, Z.hI1]
          simp
        have ha_not_verts : a ∉ S.triangle.verts := by
          have ha_ne_v1 : a ≠ q1 := by
            unfold Problem97.FiniteEndpointShell.I2 at hA2
            exact (Finset.mem_erase.mp hA2).1
          have ha_ne_v3 : a ≠ S.triangle.v3 := by
            unfold Problem97.FiniteEndpointShell.I2 at hA2
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).1
          have ha_ne_v2 : a ≠ q2 := by
            intro h
            have : q2 ∈ S.CP.C2 := by simpa [h] using haC2
            exact S.CP.v2_notin_C2 this
          simp [Problem97.MoserTriangle.verts, q1, q2, ha_ne_v1, ha_ne_v2, ha_ne_v3]
        have hone_a := S.CP.nonmoser_in_one a haA ha_not_verts
        have haI1 : a ∈ S.I1 := by simpa [hqa2] using hqI1
        have haC1 : a ∈ S.CP.C1 := by
          unfold Problem97.FiniteEndpointShell.I1 at haI1
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase haI1)
        have : False := by
          have hone_a' : (2 + if a ∈ S.CP.C3 then 1 else 0) = 1 := by
            simpa [haC1, haC2] using hone_a
          by_cases haC3 : a ∈ S.CP.C3 <;> simp [haC3] at hone_a'
        exact False.elim this
      · have hyc_pos : 0 < Y a * yc := by
          have hdisk_a' : ‖a - center‖ ≤ S.Packet.radius := by
            simpa [center] using S.Packet.disk_contains_A a haA
          have hdisk_a : dist center a ≤ S.Packet.radius := by
            rw [dist_eq_norm, norm_sub_rev]
            exact hdisk_a'
          have hradius : dist center q1 = S.Packet.radius := by
            rw [dist_comm, dist_eq_norm]
            exact S.Packet.moser_on_boundary_1
          have hdist_sq : dist center a ^ 2 ≤ dist center q1 ^ 2 := by
            have hnonneg_a : 0 ≤ dist center a := dist_nonneg
            have hnonneg_q1 : 0 ≤ dist center q1 := dist_nonneg
            nlinarith only [hdisk_a, hradius, hnonneg_a, hnonneg_q1]
          rw [hdist_center_sq a, hdist_center_sq q1, haX, hX_q1, hY_q1] at hdist_sq
          nlinarith only [hu_sq_pos, hdist_sq, haYsq]
        have hq_out : dist center q > S.Packet.radius := by
          have hradius : dist center q1 = S.Packet.radius := by
            rw [dist_comm, dist_eq_norm]
            exact S.Packet.moser_on_boundary_1
          have hdist_sq_q :
              dist center q ^ 2 > S.Packet.radius ^ 2 := by
            rw [hdist_center_sq q]
            have hradius_sq :
                S.Packet.radius ^ 2 = ((1 / 2 : ℝ) ^ 2 + yc ^ 2) * ‖u‖ ^ 2 := by
              have hq1sq := hdist_center_sq q1
              rw [hradius, hX_q1, hY_q1] at hq1sq
              nlinarith only [hq1sq]
            rw [hradius_sq]
            have hqY : Y q = -Y a := by
              exact hopp
            rw [hqX, hqY]
            nlinarith only [hu_sq_pos, haYsq, hyc_pos]
          have hrad_nn : 0 ≤ S.Packet.radius := le_of_lt S.Packet.radius_pos
          have hdist_nn : 0 ≤ dist center q := dist_nonneg
          nlinarith only [hdist_sq_q, hrad_nn, hdist_nn]
        have hdisk_q' : ‖q - center‖ ≤ S.Packet.radius := by
          simpa [center] using S.Packet.disk_contains_A q hqA
        have hdisk_q : dist center q ≤ S.Packet.radius := by
          rw [dist_eq_norm, norm_sub_rev]
          exact hdisk_q'
        exact False.elim (not_le_of_gt hq_out hdisk_q)
    rcases Finset.mem_insert.mp hqrest with hqb1 | hqv3
    · have hq_b1 : q = Z.b1 := by simpa using hqb1
      rcases hy_cases with hsame | hopp
      · have hqb2 : q = a := by
          have hsub : q - M = a - M := by
            calc
              q - M = X q • u + Y q • nvec := by rw [hsum_pt q]
              _ = 0 • u + Y a • nvec := by simpa [hqX, hsame]
              _ = X a • u + Y a • nvec := by simpa [haX]
              _ = a - M := by rw [hsum_pt a]
          have hadd := congrArg (fun t : ℝ² => t + M) hsub
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
        have hqI1 : q ∈ S.I1 := by
          rw [hq_b1, Z.hI1]
          simp
        have ha_not_verts : a ∉ S.triangle.verts := by
          have ha_ne_v1 : a ≠ q1 := by
            unfold Problem97.FiniteEndpointShell.I2 at hA2
            exact (Finset.mem_erase.mp hA2).1
          have ha_ne_v3 : a ≠ S.triangle.v3 := by
            unfold Problem97.FiniteEndpointShell.I2 at hA2
            exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA2).2).1
          have ha_ne_v2 : a ≠ q2 := by
            intro h
            have : q2 ∈ S.CP.C2 := by simpa [h] using haC2
            exact S.CP.v2_notin_C2 this
          simp [Problem97.MoserTriangle.verts, q1, q2, ha_ne_v1, ha_ne_v2, ha_ne_v3]
        have hone_a := S.CP.nonmoser_in_one a haA ha_not_verts
        have haI1 : a ∈ S.I1 := by simpa [hqb2] using hqI1
        have haC1 : a ∈ S.CP.C1 := by
          unfold Problem97.FiniteEndpointShell.I1 at haI1
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase haI1)
        have : False := by
          have hone_a' : (2 + if a ∈ S.CP.C3 then 1 else 0) = 1 := by
            simpa [haC1, haC2] using hone_a
          by_cases haC3 : a ∈ S.CP.C3 <;> simp [haC3] at hone_a'
        exact False.elim this
      · have hyc_pos : 0 < Y a * yc := by
          have hdisk_a' : ‖a - center‖ ≤ S.Packet.radius := by
            simpa [center] using S.Packet.disk_contains_A a haA
          have hdisk_a : dist center a ≤ S.Packet.radius := by
            rw [dist_eq_norm, norm_sub_rev]
            exact hdisk_a'
          have hradius : dist center q1 = S.Packet.radius := by
            rw [dist_comm, dist_eq_norm]
            exact S.Packet.moser_on_boundary_1
          have hdist_sq : dist center a ^ 2 ≤ dist center q1 ^ 2 := by
            have hnonneg_a : 0 ≤ dist center a := dist_nonneg
            have hnonneg_q1 : 0 ≤ dist center q1 := dist_nonneg
            nlinarith only [hdisk_a, hradius, hnonneg_a, hnonneg_q1]
          rw [hdist_center_sq a, hdist_center_sq q1, haX, hX_q1, hY_q1] at hdist_sq
          nlinarith only [hu_sq_pos, hdist_sq, haYsq]
        have hq_out : dist center q > S.Packet.radius := by
          have hradius : dist center q1 = S.Packet.radius := by
            rw [dist_comm, dist_eq_norm]
            exact S.Packet.moser_on_boundary_1
          have hdist_sq_q :
              dist center q ^ 2 > S.Packet.radius ^ 2 := by
            rw [hdist_center_sq q]
            have hradius_sq :
                S.Packet.radius ^ 2 = ((1 / 2 : ℝ) ^ 2 + yc ^ 2) * ‖u‖ ^ 2 := by
              have hq1sq := hdist_center_sq q1
              rw [hradius, hX_q1, hY_q1] at hq1sq
              nlinarith only [hq1sq]
            rw [hqX, hopp, hradius_sq]
            nlinarith only [hu_sq_pos, haYsq, hyc_pos]
          have hrad_nn : 0 ≤ S.Packet.radius := le_of_lt S.Packet.radius_pos
          have hdist_nn : 0 ≤ dist center q := dist_nonneg
          nlinarith only [hdist_sq_q, hrad_nn, hdist_nn]
        have hdisk_q' : ‖q - center‖ ≤ S.Packet.radius := by
          simpa [center] using S.Packet.disk_contains_A q hqA
        have hdisk_q : dist center q ≤ S.Packet.radius := by
          rw [dist_eq_norm, norm_sub_rev]
          exact hdisk_q'
        exact False.elim (not_le_of_gt hq_out hdisk_q)
    simpa using hqv3
  have hcore := (p2mCoreSupport S).coreSelector_v1 hr hcard
  rcases hcore with ⟨-, hI1sub, -, -⟩
  have hpT2 : p ∈ S.witnessClassAt_v2 s := by
    have hpmem : p ∈ ({p} : Finset ℝ²) := by simp
    rw [← hpeq] at hpmem
    exact (Finset.mem_inter.mp hpmem).1
  rcases Finset.mem_insert.mp hp with hpa1 | hp
  · have hpa1' : p = Z.a1 := by simpa using hpa1
    have ha1I1 : Z.a1 ∈ S.I1 := by
      rw [Z.hI1]
      simp
    have ha1T1 : Z.a1 ∈ S.witnessClassAt_v1 r := hI1sub ha1I1
    have hpv3 : p = S.triangle.v3 := hforce p hp hpT2 (by simpa [hpa1'] using ha1T1)
    simpa [hpv3] using hpeq
  rcases Finset.mem_insert.mp hp with hpb1 | hpv3
  · have hpb1' : p = Z.b1 := by simpa using hpb1
    have hb1I1 : Z.b1 ∈ S.I1 := by
      rw [Z.hI1]
      simp
    have hb1T1 : Z.b1 ∈ S.witnessClassAt_v1 r := hI1sub hb1I1
    have hp123 : p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) := by
      simp [hpb1']
    have hpv3 : p = S.triangle.v3 := hforce p hp123 hpT2 (by simpa [hpb1'] using hb1T1)
    simpa [hpv3] using hpeq
  have hpv3' : p = S.triangle.v3 := by simpa using hpv3
  simpa [hpv3'] using hpeq
theorem selectorShape_v2_q_eq_v1_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hr : 0 < r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s) :
    S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
  classical
  let T := S.witnessClassAt_v2 s
  have hC1eq :
      T ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) :=
    S.selectorShape_v2_q_eq_v1_forces_v3 (Z := Z) (r := r) (s := s) hr hcard hbranch
  rcases hbranch with ⟨⟨-, _, _⟩, _, hpacket⟩
  rcases hpacket with ⟨hTcard, hI2sub, _, _, _, hqeq⟩
  have ha2I2 : Z.a2 ∈ S.I2 := by
    rw [Z.hI2]
    simp
  have hb2I2 : Z.b2 ∈ S.I2 := by
    rw [Z.hI2]
    simp
  have ha2T : Z.a2 ∈ T := hI2sub ha2I2
  have hb2T : Z.b2 ∈ T := hI2sub hb2I2
  have hv3T : S.triangle.v3 ∈ T := by
    have hv3mem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    rw [← hC1eq] at hv3mem
    exact (Finset.mem_inter.mp hv3mem).1
  have hv1T : S.triangle.v1 ∈ T := by
    have hv1mem : S.triangle.v1 ∈ ({S.triangle.v1} : Finset ℝ²) := by simp
    rw [← hqeq] at hv1mem
    exact (Finset.mem_inter.mp hv1mem).1
  have ha2_ne_b2 : Z.a2 ≠ Z.b2 := by
    have hI2card : ({Z.a2, Z.b2} : Finset ℝ²).card = 2 := by
      simpa [Z.hI2] using (p2mCoreSupport S).I2_card_eq_two
    intro h
    simp [h] at hI2card
  have ha2_ne_v1 : Z.a2 ≠ S.triangle.v1 := by
    unfold Problem97.FiniteEndpointShell.I2 at ha2I2
    exact (Finset.mem_erase.mp ha2I2).1
  have hb2_ne_v1 : Z.b2 ≠ S.triangle.v1 := by
    unfold Problem97.FiniteEndpointShell.I2 at hb2I2
    exact (Finset.mem_erase.mp hb2I2).1
  have ha2_ne_v3 : Z.a2 ≠ S.triangle.v3 := by
    unfold Problem97.FiniteEndpointShell.I2 at ha2I2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp ha2I2).2).1
  have hb2_ne_v3 : Z.b2 ≠ S.triangle.v3 := by
    unfold Problem97.FiniteEndpointShell.I2 at hb2I2
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hb2I2).2).1
  have hUsub :
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) ⊆ T := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha2T
    · exact hb2T
    · exact hv3T
    · exact hv1T
  have hUcard :
      (insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))).card = 4 := by
    simp [ha2_ne_b2, ha2_ne_v1, hb2_ne_v1, ha2_ne_v3, hb2_ne_v3, S.triangle.v13_ne,
      S.triangle.v13_ne.symm]
  have hTle :
      T.card ≤ (insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))).card := by
    rw [hTcard, hUcard]
  exact (Finset.eq_of_subset_of_card_le hUsub hTle).symm
theorem selectorShape_v2_q_eq_v1_exact_packet_of_b2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hr : 0 < r)
    (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hbranch : FormBv1B2SelectorV2Qv1Packet S Z r s) :
    S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
  rcases hbranch with ⟨⟨hb2I2, hb2eq, hv2eq⟩, hs, hpacket⟩
  have hbranch' : FormBv1A2SelectorV2Qv1Packet S (Z.swapI2) r s := by
    refine ⟨?_, hs, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [ZeroDefectCapLayout.swapI2] using hb2I2
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hb2eq
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hv2eq
    · simpa [SelectorV2Qv1Packet, ZeroDefectCapLayout.swapI2] using hpacket
  have hswap :=
    S.selectorShape_v2_q_eq_v1_exact_packet (Z := Z.swapI2) (r := r) (s := s) hr hcard hbranch'
  ext x
  simpa [ZeroDefectCapLayout.swapI2, hswap, Finset.mem_insert, Finset.mem_singleton,
    or_left_comm, or_assoc]
theorem v1v3_longer_than_base_of_exact_packet_of_b2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s : ℝ}
    (hbranch : FormBv1B2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
    dist S.triangle.v1 S.triangle.v2 < dist S.triangle.v1 S.triangle.v3 := by
  rcases hbranch with ⟨⟨hb2I2, hb2eq, hv2eq⟩, hs, hpacket⟩
  have hbranch' : FormBv1A2SelectorV2Qv1Packet S (Z.swapI2) r s := by
    refine ⟨?_, hs, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [ZeroDefectCapLayout.swapI2] using hb2I2
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hb2eq
      · simpa [FormBv1A2Packet, ZeroDefectCapLayout.swapI2] using hv2eq
    · simpa [SelectorV2Qv1Packet, ZeroDefectCapLayout.swapI2] using hpacket
  have hswap :
      S.witnessClassAt_v2 s =
        insert (Z.swapI2).a2
          (insert (Z.swapI2).b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) := by
    ext x
    simpa [ZeroDefectCapLayout.swapI2, hexact, Finset.mem_insert, Finset.mem_singleton,
      or_left_comm, or_assoc]
  simpa [ZeroDefectCapLayout.swapI2] using
    ((p2mBranchSupport S Z.swapI2).v1v3_longer_than_base_of_exact_packet hbranch' hswap)
theorem selectorShape_v3_q_eq_v1_impossible_of_b2_exact_packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) {r s t : ℝ}
    (hbranch : FormBv1B2SelectorV2Qv1Packet S Z r s)
    (hexact : S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)))
    (hpacket3 : SelectorV3Qv1Packet S Z t) :
    False := by
  have hlong := S.v1v3_longer_than_base_of_exact_packet_of_b2 Z hbranch hexact
  have hv3T : S.triangle.v3 ∈ S.witnessClassAt_v2 s := by
    have hv3mem : S.triangle.v3 ∈ ({S.triangle.v3} : Finset ℝ²) := by simp
    simpa [hexact] using hv3mem
  have hv1T : S.triangle.v1 ∈ S.witnessClassAt_v2 s := by
    have hv1mem : S.triangle.v1 ∈ ({S.triangle.v1} : Finset ℝ²) := by simp
    simpa [hexact] using hv1mem
  have hv3dist : dist S.triangle.v2 S.triangle.v3 = s := by
    simpa using (Finset.mem_filter.mp hv3T).2
  have hv1dist : dist S.triangle.v2 S.triangle.v1 = s := by
    simpa using (Finset.mem_filter.mp hv1T).2
  have hv2v1 : dist S.triangle.v3 S.triangle.v2 < dist S.triangle.v3 S.triangle.v1 := by
    calc
      dist S.triangle.v3 S.triangle.v2 = dist S.triangle.v2 S.triangle.v3 := by rw [dist_comm]
      _ = dist S.triangle.v2 S.triangle.v1 := by rw [hv3dist, hv1dist]
      _ = dist S.triangle.v1 S.triangle.v2 := by rw [dist_comm]
      _ < dist S.triangle.v1 S.triangle.v3 := hlong
      _ = dist S.triangle.v3 S.triangle.v1 := by rw [dist_comm]
  exact (p2mCoreSupport S).selectorShape_v3_q_eq_v1_impossible Z hpacket3 hv2v1
theorem n4c_forms_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
    (hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1) :
    S.IsFormA_v1 r ∨ S.IsFormB_v1 r ∨ S.IsFormC_v1 r := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v1 r
  have hcore := (p2mCoreSupport S).coreSelector_v1 hr hcard
  rcases hcore with ⟨hTcard, hI1sub, hC2le, hC3le⟩
  have hTcard' : T.card = 4 := by simpa [T] using hTcard
  have hC2le' : (T ∩ S.CP.C2).card ≤ 1 := by simpa [T] using hC2le
  have hC3le' : (T ∩ S.CP.C3).card ≤ 1 := by simpa [T] using hC3le
  have hI1two : S.I1.card = 2 := (p2mCoreSupport S).I1_card_eq_two
  have hI1sub' : S.I1 ⊆ T ∩ S.I1 := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hI1sub hz, hz⟩
  have hTminus_eq_two : (T \ S.I1).card = 2 := by
    have hsplit : (T \ S.I1).card + (T ∩ S.I1).card = T.card := by
      simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I1
    have hI1ge : S.I1.card ≤ (T ∩ S.I1).card := Finset.card_le_card hI1sub'
    have hI1le : (T ∩ S.I1).card ≤ S.I1.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have hcover :
      T \ S.I1 ⊆ (T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3) := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnotI1⟩
    have hxA : x ∈ A := (Finset.mem_filter.mp hxT).1
    by_cases hxv3 : x = S.triangle.v3
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv3] using S.CP.v3_mem_C2⟩
    by_cases hxv2 : x = S.triangle.v2
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv2] using S.CP.v2_mem_C3⟩
    by_cases hxv1 : x = S.triangle.v1
    · have hv1not : S.triangle.v1 ∉ T := by
        intro hv1T
        have hv1eq : dist S.triangle.v1 S.triangle.v1 = r :=
          (Finset.mem_filter.mp hv1T).2
        have h0r : (0 : ℝ) = r := by simpa using hv1eq
        nlinarith only [hr, h0r]
      exact False.elim (hv1not (hxv1 ▸ hxT))
    have hxnonmoser : x ∉ S.triangle.verts := by
      simp [Problem97.MoserTriangle.verts, hxv1, hxv2, hxv3]
    have hxnotC1 : x ∉ S.CP.C1 := by
      intro hxC1
      have hxI1 : x ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hxv3, Finset.mem_erase.mpr ⟨hxv2, hxC1⟩⟩
      exact hxnotI1 hxI1
    have hone := S.CP.nonmoser_in_one x hxA hxnonmoser
    by_cases hxC2 : x ∈ S.CP.C2
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxT, hxC2⟩))
    · have hxC3 : x ∈ S.CP.C3 := by
        by_cases hxC3 : x ∈ S.CP.C3
        · exact hxC3
        · have : (0 : ℕ) = 1 := by
            simpa [hxnotC1, hxC2, hxC3] using hone
          omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxT, hxC3⟩))
  have hUnion_le :
      ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card ≤ 2 := by
    calc
      ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card
          ≤ (T ∩ S.CP.C2).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hUnion_eq_two :
      ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card = 2 := by
    have hTminus_le : (T \ S.I1).card ≤ ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card :=
      Finset.card_le_card hcover
    omega
  have hsum_eq_two : (T ∩ S.CP.C2).card + (T ∩ S.CP.C3).card = 2 := by
    have hUnion_le_sum : ((T ∩ S.CP.C2) ∪ (T ∩ S.CP.C3)).card ≤
        (T ∩ S.CP.C2).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
    omega
  have hC2eq1 : (T ∩ S.CP.C2).card = 1 := by
    omega
  have hC3eq1 : (T ∩ S.CP.C3).card = 1 := by
    omega
  obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hC2eq1
  obtain ⟨y, hyeq⟩ := Finset.card_eq_one.mp hC3eq1
  have hxT : x ∈ T := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).1
  have hyT : y ∈ T := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).1
  have hxC2 : x ∈ S.CP.C2 := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).2
  have hyC3 : y ∈ S.CP.C3 := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).2
  have hv1notT : S.triangle.v1 ∉ T := by
    intro hv1T
    have hv1eq : dist S.triangle.v1 S.triangle.v1 = r := (Finset.mem_filter.mp hv1T).2
    have h0r : (0 : ℝ) = r := by simpa using hv1eq
    nlinarith only [hr, h0r]
  have hx_ne_v1 : x ≠ S.triangle.v1 := by
    intro h
    exact hv1notT (h ▸ hxT)
  have hy_ne_v1 : y ≠ S.triangle.v1 := by
    intro h
    exact hv1notT (h ▸ hyT)
  by_cases hxv3 : x = S.triangle.v3
  · by_cases hyv2 : y = S.triangle.v2
    · have hsubC1 : T ⊆ S.CP.C1 := by
        intro z hz
        by_cases hzI1 : z ∈ S.I1
        · unfold I1 at hzI1
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzI1).2).2
        · have hzout : z ∈ T \ S.I1 := Finset.mem_sdiff.mpr ⟨hz, hzI1⟩
          have hzcover := hcover hzout
          rcases Finset.mem_union.mp hzcover with hzC2 | hzC3
          · have : z = x := by
              rw [hxeq] at hzC2
              simpa using hzC2
            simpa [this, hxv3] using S.CP.v3_mem_C1
          · have : z = y := by
              rw [hyeq] at hzC3
              simpa using hzC3
            simpa [this, hyv2] using S.CP.v2_mem_C1
      exact False.elim (hesc hsubC1)
    · have hyI3 : y ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hyv2, Finset.mem_erase.mpr ⟨hy_ne_v1, hyC3⟩⟩
      exact Or.inr (Or.inr ⟨y, hyI3, by simpa [T, hxv3] using hxeq, by simpa [T] using hyeq⟩)
  · by_cases hyv2 : y = S.triangle.v2
    · have hxI2 : x ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hx_ne_v1, Finset.mem_erase.mpr ⟨hxv3, hxC2⟩⟩
      exact Or.inr (Or.inl ⟨x, hxI2, by simpa [T] using hxeq, by simpa [T, hyv2] using hyeq⟩)
    · have hxI2 : x ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hx_ne_v1, Finset.mem_erase.mpr ⟨hxv3, hxC2⟩⟩
      have hyI3 : y ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hyv2, Finset.mem_erase.mpr ⟨hy_ne_v1, hyC3⟩⟩
      exact Or.inl ⟨x, y, hxI2, hyI3, by simpa [T] using hxeq, by simpa [T] using hyeq⟩
theorem n4c_forms_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
    (hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2) :
    S.IsFormA_v2 r ∨ S.IsFormB_v2 r ∨ S.IsFormC_v2 r := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v2 r
  have hcore := (p2mCoreSupport S).coreSelector_v2 hr hcard
  rcases hcore with ⟨hTcard, hI2sub, hC1le, hC3le⟩
  have hTcard' : T.card = 4 := by simpa [T] using hTcard
  have hC1le' : (T ∩ S.CP.C1).card ≤ 1 := by simpa [T] using hC1le
  have hC3le' : (T ∩ S.CP.C3).card ≤ 1 := by simpa [T] using hC3le
  have hI2two : S.I2.card = 2 := (p2mCoreSupport S).I2_card_eq_two
  have hI2sub' : S.I2 ⊆ T ∩ S.I2 := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hI2sub hz, hz⟩
  have hTminus_eq_two : (T \ S.I2).card = 2 := by
    have hsplit : (T \ S.I2).card + (T ∩ S.I2).card = T.card := by
      simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I2
    have hI2ge : S.I2.card ≤ (T ∩ S.I2).card := Finset.card_le_card hI2sub'
    have hI2le : (T ∩ S.I2).card ≤ S.I2.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have hcover :
      T \ S.I2 ⊆ (T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3) := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnotI2⟩
    have hxA : x ∈ A := (Finset.mem_filter.mp hxT).1
    by_cases hxv1 : x = S.triangle.v1
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv1] using S.CP.v1_mem_C3⟩
    by_cases hxv3 : x = S.triangle.v3
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv3] using S.CP.v3_mem_C1⟩
    by_cases hxv2 : x = S.triangle.v2
    · have hv2not : S.triangle.v2 ∉ T := by
        intro hv2T
        have hv2eq : dist S.triangle.v2 S.triangle.v2 = r :=
          (Finset.mem_filter.mp hv2T).2
        have h0r : (0 : ℝ) = r := by simpa using hv2eq
        nlinarith only [hr, h0r]
      exact False.elim (hv2not (hxv2 ▸ hxT))
    have hxnonmoser : x ∉ S.triangle.verts := by
      simp [Problem97.MoserTriangle.verts, hxv1, hxv2, hxv3]
    have hxnotC2 : x ∉ S.CP.C2 := by
      intro hxC2
      have hxI2 : x ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hxv1, Finset.mem_erase.mpr ⟨hxv3, hxC2⟩⟩
      exact hxnotI2 hxI2
    have hone := S.CP.nonmoser_in_one x hxA hxnonmoser
    by_cases hxC1 : x ∈ S.CP.C1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxT, hxC1⟩))
    · have hxC3 : x ∈ S.CP.C3 := by
        by_cases hxC3 : x ∈ S.CP.C3
        · exact hxC3
        · have : (0 : ℕ) = 1 := by
            simpa [hxC1, hxnotC2, hxC3] using hone
          omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxT, hxC3⟩))
  have hUnion_le :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card ≤ 2 := by
    calc
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card
          ≤ (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hUnion_eq_two :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card = 2 := by
    have hTminus_le : (T \ S.I2).card ≤ ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card :=
      Finset.card_le_card hcover
    omega
  have hsum_eq_two : (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card = 2 := by
    have hUnion_le_sum : ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C3)).card ≤
        (T ∩ S.CP.C1).card + (T ∩ S.CP.C3).card := Finset.card_union_le _ _
    omega
  have hC1eq1 : (T ∩ S.CP.C1).card = 1 := by omega
  have hC3eq1 : (T ∩ S.CP.C3).card = 1 := by omega
  obtain ⟨y, hyeq⟩ := Finset.card_eq_one.mp hC1eq1
  obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hC3eq1
  have hxT : x ∈ T := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).1
  have hyT : y ∈ T := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).1
  have hxC3 : x ∈ S.CP.C3 := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).2
  have hyC1 : y ∈ S.CP.C1 := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).2
  have hv2notT : S.triangle.v2 ∉ T := by
    intro hv2T
    have hv2eq : dist S.triangle.v2 S.triangle.v2 = r := (Finset.mem_filter.mp hv2T).2
    have h0r : (0 : ℝ) = r := by simpa using hv2eq
    nlinarith only [hr, h0r]
  have hx_ne_v2 : x ≠ S.triangle.v2 := by
    intro h
    exact hv2notT (h ▸ hxT)
  have hy_ne_v2 : y ≠ S.triangle.v2 := by
    intro h
    exact hv2notT (h ▸ hyT)
  by_cases hxv1 : x = S.triangle.v1
  · by_cases hyv3 : y = S.triangle.v3
    · have hsubC2 : T ⊆ S.CP.C2 := by
        intro z hz
        by_cases hzI2 : z ∈ S.I2
        · unfold I2 at hzI2
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzI2).2).2
        · have hzout : z ∈ T \ S.I2 := Finset.mem_sdiff.mpr ⟨hz, hzI2⟩
          have hzcover := hcover hzout
          rcases Finset.mem_union.mp hzcover with hzC1 | hzC3
          · have : z = y := by
              rw [hyeq] at hzC1
              simpa using hzC1
            simpa [this, hyv3] using S.CP.v3_mem_C2
          · have : z = x := by
              rw [hxeq] at hzC3
              simpa using hzC3
            simpa [this, hxv1] using S.CP.v1_mem_C2
      exact False.elim (hesc hsubC2)
    · have hyI1 : y ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hyv3, Finset.mem_erase.mpr ⟨hy_ne_v2, hyC1⟩⟩
      exact Or.inr (Or.inr ⟨y, hyI1, by simpa [T, hxv1] using hxeq, by simpa [T] using hyeq⟩)
  · by_cases hyv3 : y = S.triangle.v3
    · have hxI3 : x ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hx_ne_v2, Finset.mem_erase.mpr ⟨hxv1, hxC3⟩⟩
      exact Or.inr (Or.inl ⟨x, hxI3, by simpa [T] using hxeq, by simpa [T, hyv3] using hyeq⟩)
    · have hxI3 : x ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hx_ne_v2, Finset.mem_erase.mpr ⟨hxv1, hxC3⟩⟩
      have hyI1 : y ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hyv3, Finset.mem_erase.mpr ⟨hy_ne_v2, hyC1⟩⟩
      exact Or.inl ⟨x, y, hxI3, hyI1, by simpa [T] using hxeq, by simpa [T] using hyeq⟩
theorem n4c_forms_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) {r : ℝ}
    (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
    (hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3) :
    S.IsFormA_v3 r ∨ S.IsFormB_v3 r ∨ S.IsFormC_v3 r := by
  classical
  let T : Finset ℝ² := S.witnessClassAt_v3 r
  have hcore := (p2mCoreSupport S).coreSelector_v3 hr hcard
  rcases hcore with ⟨hTcard, hI3sub, hC1le, hC2le⟩
  have hTcard' : T.card = 4 := by simpa [T] using hTcard
  have hC1le' : (T ∩ S.CP.C1).card ≤ 1 := by simpa [T] using hC1le
  have hC2le' : (T ∩ S.CP.C2).card ≤ 1 := by simpa [T] using hC2le
  have hI3two : S.I3.card = 2 := (p2mCoreSupport S).I3_card_eq_two
  have hI3sub' : S.I3 ⊆ T ∩ S.I3 := by
    intro z hz
    exact Finset.mem_inter.mpr ⟨hI3sub hz, hz⟩
  have hTminus_eq_two : (T \ S.I3).card = 2 := by
    have hsplit : (T \ S.I3).card + (T ∩ S.I3).card = T.card := by
      simpa [T, Finset.inter_comm] using Finset.card_sdiff_add_card_inter T S.I3
    have hI3ge : S.I3.card ≤ (T ∩ S.I3).card := Finset.card_le_card hI3sub'
    have hI3le : (T ∩ S.I3).card ≤ S.I3.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have hcover :
      T \ S.I3 ⊆ (T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2) := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnotI3⟩
    have hxA : x ∈ A := (Finset.mem_filter.mp hxT).1
    by_cases hxv2 : x = S.triangle.v2
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv2] using S.CP.v2_mem_C1⟩
    by_cases hxv1 : x = S.triangle.v1
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxT, by simpa [hxv1] using S.CP.v1_mem_C2⟩
    by_cases hxv3 : x = S.triangle.v3
    · have hv3not : S.triangle.v3 ∉ T := by
        intro hv3T
        have hv3eq : dist S.triangle.v3 S.triangle.v3 = r :=
          (Finset.mem_filter.mp hv3T).2
        have h0r : (0 : ℝ) = r := by simpa using hv3eq
        nlinarith only [hr, h0r]
      exact False.elim (hv3not (hxv3 ▸ hxT))
    have hxnonmoser : x ∉ S.triangle.verts := by
      simp [Problem97.MoserTriangle.verts, hxv1, hxv2, hxv3]
    have hxnotC3 : x ∉ S.CP.C3 := by
      intro hxC3
      have hxI3 : x ∈ S.I3 := by
        unfold I3
        exact Finset.mem_erase.mpr ⟨hxv2, Finset.mem_erase.mpr ⟨hxv1, hxC3⟩⟩
      exact hxnotI3 hxI3
    have hone := S.CP.nonmoser_in_one x hxA hxnonmoser
    by_cases hxC1 : x ∈ S.CP.C1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxT, hxC1⟩))
    · have hxC2 : x ∈ S.CP.C2 := by
        by_cases hxC2 : x ∈ S.CP.C2
        · exact hxC2
        · have : (0 : ℕ) = 1 := by
            simpa [hxC1, hxC2, hxnotC3] using hone
          omega
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxT, hxC2⟩))
  have hUnion_le :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card ≤ 2 := by
    calc
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card
          ≤ (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by omega
      _ = 2 := by norm_num
  have hUnion_eq_two :
      ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card = 2 := by
    have hTminus_le : (T \ S.I3).card ≤ ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card :=
      Finset.card_le_card hcover
    omega
  have hsum_eq_two : (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card = 2 := by
    have hUnion_le_sum : ((T ∩ S.CP.C1) ∪ (T ∩ S.CP.C2)).card ≤
        (T ∩ S.CP.C1).card + (T ∩ S.CP.C2).card := Finset.card_union_le _ _
    omega
  have hC1eq1 : (T ∩ S.CP.C1).card = 1 := by omega
  have hC2eq1 : (T ∩ S.CP.C2).card = 1 := by omega
  obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hC1eq1
  obtain ⟨y, hyeq⟩ := Finset.card_eq_one.mp hC2eq1
  have hxT : x ∈ T := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).1
  have hyT : y ∈ T := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).1
  have hxC1 : x ∈ S.CP.C1 := by
    have hxmem : x ∈ ({x} : Finset ℝ²) := by simp
    rw [← hxeq] at hxmem
    exact (Finset.mem_inter.mp hxmem).2
  have hyC2 : y ∈ S.CP.C2 := by
    have hymem : y ∈ ({y} : Finset ℝ²) := by simp
    rw [← hyeq] at hymem
    exact (Finset.mem_inter.mp hymem).2
  have hv3notT : S.triangle.v3 ∉ T := by
    intro hv3T
    have hv3eq : dist S.triangle.v3 S.triangle.v3 = r := (Finset.mem_filter.mp hv3T).2
    have h0r : (0 : ℝ) = r := by simpa using hv3eq
    nlinarith only [hr, h0r]
  have hx_ne_v3 : x ≠ S.triangle.v3 := by
    intro h
    exact hv3notT (h ▸ hxT)
  have hy_ne_v3 : y ≠ S.triangle.v3 := by
    intro h
    exact hv3notT (h ▸ hyT)
  by_cases hxv2 : x = S.triangle.v2
  · by_cases hyv1 : y = S.triangle.v1
    · have hsubC3 : T ⊆ S.CP.C3 := by
        intro z hz
        by_cases hzI3 : z ∈ S.I3
        · unfold I3 at hzI3
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzI3).2).2
        · have hzout : z ∈ T \ S.I3 := Finset.mem_sdiff.mpr ⟨hz, hzI3⟩
          have hzcover := hcover hzout
          rcases Finset.mem_union.mp hzcover with hzC1 | hzC2
          · have : z = x := by
              rw [hxeq] at hzC1
              simpa using hzC1
            simpa [this, hxv2] using S.CP.v2_mem_C3
          · have : z = y := by
              rw [hyeq] at hzC2
              simpa using hzC2
            simpa [this, hyv1] using S.CP.v1_mem_C3
      exact False.elim (hesc hsubC3)
    · have hyI2 : y ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hyv1, Finset.mem_erase.mpr ⟨hy_ne_v3, hyC2⟩⟩
      exact Or.inr (Or.inr ⟨y, hyI2, by simpa [T, hxv2] using hxeq, by simpa [T] using hyeq⟩)
  · by_cases hyv1 : y = S.triangle.v1
    · have hxI1 : x ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hx_ne_v3, Finset.mem_erase.mpr ⟨hxv2, hxC1⟩⟩
      exact Or.inr (Or.inl ⟨x, hxI1, by simpa [T] using hxeq, by simpa [T, hyv1] using hyeq⟩)
    · have hxI1 : x ∈ S.I1 := by
        unfold I1
        exact Finset.mem_erase.mpr ⟨hx_ne_v3, Finset.mem_erase.mpr ⟨hxv2, hxC1⟩⟩
      have hyI2 : y ∈ S.I2 := by
        unfold I2
        exact Finset.mem_erase.mpr ⟨hyv1, Finset.mem_erase.mpr ⟨hy_ne_v3, hyC2⟩⟩
      exact Or.inl ⟨x, y, hxI1, hyI2, by simpa [T] using hxeq, by simpa [T] using hyeq⟩
abbrev N4cClassifies_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Type :=
  ∀ {r : ℝ}, 0 < r →
    4 ≤ (S.witnessClassAt_v1 r).card →
    ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1 →
    EscapedForm
abbrev N4cClassifies_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Type :=
  ∀ {r : ℝ}, 0 < r →
    4 ≤ (S.witnessClassAt_v2 r).card →
    ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2 →
    EscapedForm
abbrev N4cClassifies_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Type :=
  ∀ {r : ℝ}, 0 < r →
    4 ≤ (S.witnessClassAt_v3 r).card →
    ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3 →
    EscapedForm
noncomputable def n4cClassifies_v1
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.N4cClassifies_v1 := by
  classical
  intro r hr hcard hesc
  by_cases hA : S.IsFormA_v1 r
  · exact EscapedForm.a
  · by_cases hB : S.IsFormB_v1 r
    · exact EscapedForm.b
    · have hC : S.IsFormC_v1 r := by
        rcases S.n4c_forms_v1 hr hcard hesc with hA' | hB' | hC'
        · exact False.elim (hA hA')
        · exact False.elim (hB hB')
        · exact hC'
      exact EscapedForm.c
noncomputable def n4cClassifies_v2
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.N4cClassifies_v2 := by
  classical
  intro r hr hcard hesc
  by_cases hA : S.IsFormA_v2 r
  · exact EscapedForm.a
  · by_cases hB : S.IsFormB_v2 r
    · exact EscapedForm.b
    · have hC : S.IsFormC_v2 r := by
        rcases S.n4c_forms_v2 hr hcard hesc with hA' | hB' | hC'
        · exact False.elim (hA hA')
        · exact False.elim (hB hB')
        · exact hC'
      exact EscapedForm.c
noncomputable def n4cClassifies_v3
    {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    S.N4cClassifies_v3 := by
  classical
  intro r hr hcard hesc
  by_cases hA : S.IsFormA_v3 r
  · exact EscapedForm.a
  · by_cases hB : S.IsFormB_v3 r
    · exact EscapedForm.b
    · have hC : S.IsFormC_v3 r := by
        rcases S.n4c_forms_v3 hr hcard hesc with hA' | hB' | hC'
        · exact False.elim (hA hA')
        · exact False.elim (hB hB')
        · exact hC'
      exact EscapedForm.c
abbrev N4dExcludes_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (classify : S.N4cClassifies_v1) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
      (hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1),
    False
abbrev N4dExcludes_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (classify : S.N4cClassifies_v2) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
      (hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2),
    False
abbrev N4dExcludes_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (classify : S.N4cClassifies_v3) : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
      (hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3),
    False
theorem n4dExcludes_v1_of_forms
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hA : S.N4dExcludesFormA_v1)
    (hB : S.N4dExcludesFormB_v1)
    (hC : S.N4dExcludesFormC_v1) :
    S.N4dExcludes_v1 S.n4cClassifies_v1 := by
  intro r hr hcard hesc
  rcases S.n4c_forms_v1 hr hcard hesc with hform | hform | hform
  · exact hA hr hcard hesc hform
  · exact hB hr hcard hesc hform
  · exact hC hr hcard hesc hform
theorem n4dExcludes_v2_of_forms
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hA : S.N4dExcludesFormA_v2)
    (hB : S.N4dExcludesFormB_v2)
    (hC : S.N4dExcludesFormC_v2) :
    S.N4dExcludes_v2 S.n4cClassifies_v2 := by
  intro r hr hcard hesc
  rcases S.n4c_forms_v2 hr hcard hesc with hform | hform | hform
  · exact hA hr hcard hesc hform
  · exact hB hr hcard hesc hform
  · exact hC hr hcard hesc hform
theorem n4dExcludes_v3_of_forms
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hA : S.N4dExcludesFormA_v3)
    (hB : S.N4dExcludesFormB_v3)
    (hC : S.N4dExcludesFormC_v3) :
    S.N4dExcludes_v3 S.n4cClassifies_v3 := by
  intro r hr hcard hesc
  rcases S.n4c_forms_v3 hr hcard hesc with hform | hform | hform
  · exact hA hr hcard hesc hform
  · exact hB hr hcard hesc hform
  · exact hC hr hcard hesc hform
theorem n4eCapContainment_of_n4c_n4d
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (hClass1 : S.N4cClassifies_v1) (hClass2 : S.N4cClassifies_v2)
    (hClass3 : S.N4cClassifies_v3)
    (hExcl1 : S.N4dExcludes_v1 hClass1)
    (hExcl2 : S.N4dExcludes_v2 hClass2)
    (hExcl3 : S.N4dExcludes_v3 hClass3) :
    S.N4eCapContainment := by
  constructor
  · intro r hr hcard
    by_contra hsub
    exact hExcl1 hr hcard hsub
  constructor
  · intro r hr hcard
    by_contra hsub
    exact hExcl2 hr hcard hsub
  · intro r hr hcard
    by_contra hsub
    exact hExcl3 hr hcard hsub

end FiniteEndpointShell
end Problem97
end Batch3N9
end Batch3N9Unit051CapContainment

open scoped EuclideanGeometry

theorem solution {A : Finset ℝ²}
    (S : Batch3N9.Problem97.FiniteEndpointShell A)
    (hA1 : S.N4dExcludesFormA_v1) (hB1 : S.N4dExcludesFormB_v1)
    (hC1 : S.N4dExcludesFormC_v1) (hB2 : S.N4dExcludesFormB_v2)
    (hcyclic : S.N4dExcludesFormA_v2 ∧ S.N4dExcludesFormC_v2 ∧
      S.N4dExcludesFormA_v3 ∧ S.N4dExcludesFormB_v3 ∧ S.N4dExcludesFormC_v3) :
    S.N4eCapContainment := by
  rcases hcyclic with ⟨hA2, hC2, hA3, hB3, hC3⟩
  exact S.n4eCapContainment_of_n4c_n4d
    S.n4cClassifies_v1 S.n4cClassifies_v2 S.n4cClassifies_v3
    (S.n4dExcludes_v1_of_forms hA1 (Erdos9796FiniteNine.form_b_v1 S) hC1)
    (S.n4dExcludes_v2_of_forms hA2 hB2 hC2)
    (S.n4dExcludes_v3_of_forms hA3 hB3 hC3)
