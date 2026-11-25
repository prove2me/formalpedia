-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.padic_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:46:31.033611+00:00
-- url     : https://prove2.me/submissions/9633e5e0-4029-4c18-a5e8-269d0b23eced

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_modK_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_mem_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_lat_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_J_anti
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_nhds_basis
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_J_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_inv_bdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_loc_count
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_finite_cosets
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A6x9_out_sub_mem__bb6e5f696f0d
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_lattice_refinement_identity
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x5_modK_mul__b5e25af6776b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A6x9
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.ChangeVar := by
  classical
  intro K _ _ _ R ψ hd hn m hm Om Λ hOm hΛ hst hmod
  obtain ⟨hOo, hOc, hOu, hOζ⟩ := hOm
  obtain ⟨π, hπ, hπ'⟩ := hd.unif
  obtain ⟨su, hsu⟩ := hn (m + 1) (by omega)
  obtain ⟨si, hsi⟩ : ∃ si : K, si = ((su⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hs : ((m + 1 : ℕ) : K) * si = 1 := by rw [← hsu, hsi]; simp
  obtain ⟨k, hk⟩ := hπ' si
  obtain ⟨k', hk'⟩ := inv_bdd π hd hn hπ hπ' hOc hOu
  obtain ⟨i, hi⟩ := nhds_basis π hd hn hπ hπ' (Λ : Set K) (hΛ.1.mem_nhds Λ.zero_mem)
  obtain ⟨j, hj⟩ : ∃ j, j = k + 1 + k' + i := ⟨_, rfl⟩
  have hBΛ : mulR R ((π : K) ^ j) ≤ Λ := fun x hx => hi (J_anti π hπ (by omega) hx)
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨_, J_nhds π hd (j + k + k'), ?_⟩
  intro t cr f ht hcr hf
  obtain ⟨r, hr, htr⟩ := mem_mulR.1 ht
  obtain ⟨T, hT⟩ : ∃ T : Kˣ, T = (-t) ^ m := ⟨_, rfl⟩
  have hTv : (T : K) = (-(t : K)) ^ m := by rw [hT]; simp
  simp only [← hT]

  have hloc : ∀ z0 ∈ Om,
      {p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ j) ∧
        p.2 ^ (m + 1) = T * cr p.1}.Finite ∧
      ({p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - z0 ∈ mulR R ((π : K) ^ j) ∧
        p.2 ^ (m + 1) = T * cr p.1}.ncard : ℝ) =
        (modK R (t : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K) * modK R z0 ^ m * modK R ((π : K) ^ j) := by
    intro z0 hz0
    obtain ⟨zu, rfl⟩ := hOu z0 hz0
    have hzi : (zu : K) * ((zu⁻¹ : Kˣ) : K) = 1 := by simp
    have hTi : ((T⁻¹ : Kˣ) : K) * (T : K) = 1 := by simp
    have hav : ((T⁻¹ * su * zu ^ m * π ^ j : Kˣ) : K) =
        ((T⁻¹ : Kˣ) : K) * ((m + 1 : ℕ) : K) * (zu : K) ^ m * (π : K) ^ j := by
      simp [hsu]
    have h1 := loc_count π hd hn hπ hπ' (i := i) hs hk hzi (hk' _ hz0 _ hzi) T cr hcr
      (T⁻¹ * su * zu ^ m * π ^ j)
      (by rw [hav, ← hj]; linear_combination ((m + 1 : ℕ) : K) * (zu : K) ^ m * (π : K) ^ j * hTi)
      (by
        have hE : ((T⁻¹ * su * zu ^ m * π ^ j : Kˣ) : K) *
            ((-r) ^ m * (π : K) ^ ((j + k) * m') * ((π : K) ^ k * si) *
              ((π : K) ^ k' * ((zu⁻¹ : Kˣ) : K)) ^ m) = 1 := by
          have hT2 : (T : K) = (-r) ^ m * (π : K) ^ (j + (j + k) * m' + k + k' * m) := by
            rw [hTv, ← htr, hm']; ring
          have e : ((T⁻¹ * su * zu ^ m * π ^ j : Kˣ) : K) *
              ((-r) ^ m * (π : K) ^ ((j + k) * m') * ((π : K) ^ k * si) *
                ((π : K) ^ k' * ((zu⁻¹ : Kˣ) : K)) ^ m) =
              (((T⁻¹ : Kˣ) : K) * ((-r) ^ m * (π : K) ^ (j + (j + k) * m' + k + k' * m))) *
                (((m + 1 : ℕ) : K) * si) * ((zu : K) * ((zu⁻¹ : Kˣ) : K)) ^ m := by
            rw [hav]; ring
          rw [e, ← hT2, hTi, hs, hzi]; simp
        rw [Units.inv_eq_of_mul_eq_one_right hE]
        exact R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem (R.neg_mem hr) _) (R.pow_mem hπ _)) hk)
          (R.pow_mem (hk' _ hz0 _ hzi) _))
    rw [← hj] at h1
    refine ⟨h1.1, ?_⟩
    rw [h1.2, hav]
    have u1 : IsUnit (((T⁻¹ : Kˣ) : K)) := Units.isUnit _
    have u2 : IsUnit (((m + 1 : ℕ) : K)) := hn _ (by omega)
    have u3 : IsUnit ((zu : K) ^ m) := zu.isUnit.pow m
    have u4 : IsUnit ((π : K) ^ j) := π.isUnit.pow j
    rw [A5x5.modK_mul' hd ((u1.mul u2).mul u3) u4, A5x5.modK_mul' hd (u1.mul u2) u3,
      A5x5.modK_mul' hd u1 u2, modK_pow hd zu.isUnit]
    congr 3
    have h2 : modK R ((T⁻¹ : Kˣ) : K) * modK R (T : K) = 1 := by
      rw [← A5x5.modK_mul' hd u1 T.isUnit, hTi, A5x5.modK_one]
    rw [hTv, modK_pow hd t.isUnit.neg, A5x5.modK_neg] at h2
    exact eq_inv_of_mul_eq_one_left h2

  obtain ⟨B, hB⟩ : ∃ B : AddSubgroup K, B = mulR R ((π : K) ^ j) := ⟨_, rfl⟩
  rw [← hB] at hBΛ
  simp only [← hB] at hloc
  have hBlat : IsLat B := by rw [hB]; exact ⟨(lat_J π hd j).op, (lat_J π hd j).cp⟩
  have hW := finite_cosets hBlat.1 hOc
  set W : Set (K ⧸ B) := {w | (Quotient.out w : K) ∈ Om} with hWdef
  set S : Set ((K ⧸ R.toAddSubgroup) × Kˣ) := {p | (p.2 : K) ∈ Om ∧ p.2 ^ (m + 1) = T * cr p.1}
    with hSdef
  have hq : ∀ p ∈ S, (((p.2 : Kˣ) : K) : K ⧸ B) ∈ W := by
    intro p hp
    have h1 := hst _ hp.1 _ (hBΛ (out_sub_mem' (B := B) (p.2 : K)))
    have e : (p.2 : K) + ((Quotient.out (((p.2 : Kˣ) : K) : K ⧸ B) : K) - (p.2 : K)) =
      (Quotient.out (((p.2 : Kˣ) : K) : K ⧸ B) : K) := by ring
    rw [e] at h1
    exact h1
  have hfib : ∀ w ∈ W, ∀ p : (K ⧸ R.toAddSubgroup) × Kˣ,
      (p ∈ S ∧ (((p.2 : Kˣ) : K) : K ⧸ B) = w) ↔
        ((p.2 : K) - (Quotient.out w : K) ∈ B ∧ p.2 ^ (m + 1) = T * cr p.1) := by
    intro w hw p
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, h2⟩
      have := out_sub_mem' (B := B) (p.2 : K)
      rw [h3] at this
      have h4 := B.neg_mem this
      rwa [neg_sub] at h4
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, h2⟩, ?_⟩
      · have := hst _ hw _ (hBΛ h1)
        rwa [add_sub_cancel] at this
      · rw [← QuotientAddGroup.out_eq' w]
        apply (QuotientAddGroup.eq).2
        have h4 := B.neg_mem h1
        rw [neg_sub, sub_eq_neg_add] at h4
        exact h4
  have hSfin : S.Finite := by
    refine (hW.biUnion (fun w hw => (hloc _ hw).1)).subset ?_
    intro p hp
    exact Set.mem_biUnion (hq p hp) ((hfib _ (hq p hp) p).1 ⟨hp, rfl⟩)

  have step1 : ∀ x : K ⧸ R.toAddSubgroup,
      (if (cr x : K) ∈ cutSet m Om t then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = T * cr x then f (z : K) else 0 else 0) =
      ∑ᶠ z : Kˣ, (fun p : (K ⧸ R.toAddSubgroup) × Kˣ => if p ∈ S then f (p.2 : K) else 0) (x, z) := by
    intro x
    by_cases hc : (cr x : K) ∈ cutSet m Om t
    · rw [if_pos hc]
      refine finsum_congr fun z => ?_
      refine if_congr ?_ rfl rfl
      constructor
      · intro h
        refine ⟨?_, h⟩
        obtain ⟨z0, hz0, h0⟩ := hc
        obtain ⟨zu, rfl⟩ := hOu z0 hz0
        have h1 : zu ^ (m + 1) = T * cr x := by
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, h0, Units.val_mul, hTv]
        have h2 : (z * zu⁻¹) ^ (m + 1) = 1 := by
          rw [mul_pow, inv_pow, h, h1, mul_inv_cancel]
        have h3 := hOζ _ hz0 ((z * zu⁻¹ : Kˣ) : K) (by
          rw [← Units.val_pow_eq_pow_val, h2, Units.val_one])
        rw [← Units.val_mul, inv_mul_cancel_right] at h3
        exact h3
      · exact fun h => h.2
    · rw [if_neg hc]
      symm
      refine finsum_eq_zero_of_forall_eq_zero fun z => if_neg ?_
      rintro ⟨h1, h2⟩
      refine hc ⟨_, h1, ?_⟩
      rw [← Units.val_pow_eq_pow_val, h2, Units.val_mul, hTv]
  have hsupp : Function.support
      (fun p : (K ⧸ R.toAddSubgroup) × Kˣ => if p ∈ S then f (p.2 : K) else 0) ⊆
      (hSfin.toFinset : Set _) := by
    intro p hp
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hp (if_neg h)
  rw [finsum_congr step1, ← finsum_curry _ (hSfin.toFinset.finite_toSet.subset hsupp),
    finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (t := hW.toFinset)
      (g := fun p : (K ⧸ R.toAddSubgroup) × Kˣ => (((p.2 : Kˣ) : K) : K ⧸ B))
      (fun p hp => by
        rw [Set.Finite.mem_toFinset] at hp ⊢
        exact hq p hp)]

  have hG : LatInv Λ Om (fun z => ((modK R z ^ m : ℝ) : ℂ) * f z) := by
    intro z hz l hl
    simp only []
    rw [hmod z hz l hl, hf z hz l hl]
  rw [← integral_lattice_refinement_identity K R ψ hd Λ B Om _ hΛ hBlat hBΛ hOc hst hG]
  unfold intLat
  have hsupp2 : Function.support (fun y : K ⧸ B => if (Quotient.out y : K) ∈ Om then
      ((modK R (Quotient.out y : K) ^ m : ℝ) : ℂ) * f (Quotient.out y : K) else 0) ⊆
      (hW.toFinset : Set _) := by
    intro y hy
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hy (if_neg h)
  rw [finsum_eq_sum_of_support_subset _ hsupp2, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have hw : (Quotient.out w : K) ∈ Om := hw
  rw [if_pos hw]
  have hset : ((hSfin.toFinset.filter
      (fun p : (K ⧸ R.toAddSubgroup) × Kˣ => (((p.2 : Kˣ) : K) : K ⧸ B) = w) : Finset _) : Set _) =
      {p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - (Quotient.out w : K) ∈ B ∧
        p.2 ^ (m + 1) = T * cr p.1} := by
    ext p
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact hfib w hw p
  have hconst : ∀ p ∈ hSfin.toFinset.filter
      (fun p : (K ⧸ R.toAddSubgroup) × Kˣ => (((p.2 : Kˣ) : K) : K ⧸ B) = w),
      (if p ∈ S then f (p.2 : K) else 0) = f (Quotient.out w : K) := by
    intro p hp
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hp
    rw [if_pos hp.1]
    have h1 := ((hfib w hw p).1 hp).1
    have h2 := hf _ hw _ (hBΛ h1)
    rwa [add_sub_cancel] at h2
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset, hset]
  have h3 := (hloc _ hw).2
  have h4 : (({p : (K ⧸ R.toAddSubgroup) × Kˣ | (p.2 : K) - (Quotient.out w : K) ∈ B ∧
        p.2 ^ (m + 1) = T * cr p.1}.ncard : ℕ) : ℂ) =
      (((modK R (t : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K) * modK R (Quotient.out w : K) ^ m *
        modK R ((π : K) ^ j) : ℝ) : ℂ) := by
    rw [← h3]; simp
  rw [h4]
  have h5 : volL R B = modK R ((π : K) ^ j) := by rw [hB]; rfl
  rw [h5]
  push_cast
  ring
end Formalism.FourierDecayAlt.P
