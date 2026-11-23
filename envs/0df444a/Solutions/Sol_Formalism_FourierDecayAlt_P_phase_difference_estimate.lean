-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_difference_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:22:40.778807+00:00
-- url     : https://prove2.me/submissions/b495a2c4-ca97-41fd-b9ca-b61dd5c9c95a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_mem_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_J_sub_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_J_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_one_add_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_pow_mem_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_bdd_of_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_binom2
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
theorem _root_.solution : Formalism.FourierDecayAlt.A6.PhaseDiff := by
  intro K _ _ _ R ψ hd hn m Om Sg hOm
  obtain ⟨π, hπ, hπ'⟩ := hd.unif
  obtain ⟨su, hsu⟩ := hn (m + 1) (by omega)
  obtain ⟨si, hsi⟩ : ∃ si : K, si = ((su⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hs : ((m + 1 : ℕ) : K) * si = 1 := by rw [← hsu, hsi]; simp
  obtain ⟨k1, hk1⟩ := bdd_of_compact π hd hπ hπ' hOm
  obtain ⟨k2, hk2⟩ := bdd_of_compact π hd hπ hπ' Sg.finite_toSet.isCompact
  obtain ⟨k3, hk3⟩ := hπ' si
  obtain ⟨k, hk⟩ : ∃ k, k = k1 + k2 + k3 := ⟨_, rfl⟩
  have hkz : ∀ z ∈ Om, (π : K) ^ k * z ∈ R := fun z hz =>
    pow_mem_mono π hπ (by omega) (hk1 z hz)
  have hkσ : ∀ σ ∈ Sg, (π : K) ^ k * σ ∈ R := fun σ hσ =>
    pow_mem_mono π hπ (by omega) (hk2 σ (by simpa using hσ))
  have hks : (π : K) ^ k * si ∈ R := pow_mem_mono π hπ (by omega) hk3
  refine ⟨_, J_nhds π hd (k + 1), _, J_nhds π hd (5 * k + 1), ?_⟩
  intro t t₁ t₂ κ ht σ hσ σ' hσ' h1 h2 hκ hκE z hz
  unfold IsShift at h1 h2
  obtain ⟨r, hr, htr⟩ := mem_mulR.1 ht
  obtain ⟨X1, hX1⟩ : ∃ X : K, X = ((t₁⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ X : K, X = ((t₂⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ X : K, X = ((t⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ X : K, X = (κ : K) - 1 := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ X : K, X = σ - σ' := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ X : K, X = d * (t₂ : K) := ⟨_, rfl⟩
  have hκ' : (κ : K) = 1 + ε := by rw [hε]; ring
  have hB : (t₂ : K) * X2 = 1 := by rw [hX2]; simp
  have hD : (t : K) * x = 1 := by rw [hx]; simp
  rw [← hX1, ← hx] at h1
  rw [← hX2, ← hx] at h2
  have hkd : (π : K) ^ k * d ∈ R := by
    rw [hdd, mul_sub]; exact R.sub_mem (hkσ σ hσ) (hkσ σ' hσ')

  have ha : σ' * (t : K) ∈ mulR R ((π : K) ^ 1) :=
    mem_mulR.2 ⟨(π : K) ^ (4 * k) * ((π : K) ^ k * σ') * r,
      R.mul_mem (R.mul_mem (R.pow_mem hπ _) (hkσ σ' hσ')) hr, by rw [← htr]; ring⟩
  obtain ⟨u, huR, hu⟩ := one_add_unit π hd hn hπ hπ' _ ha
  have ht2 : (t₂ : K) = (t : K) * u := by
    linear_combination (-(t₂ : K)) * hu + u * (-(t₂ : K) * hD - (t : K) * (t₂ : K) * h2 + (t : K) * hB)
  have hδ3 : δ = (π : K) ^ (5 * k + 1) * (d * r * u) := by rw [hδ, ht2, ← htr]; ring
  have hδR : δ ∈ R := by
    have : δ = (π : K) ^ (4 * k + 1) * ((π : K) ^ k * d) * r * u := by rw [hδ3]; ring
    rw [this]
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem hπ _) hkd) hr) huR
  have hεR : ε ∈ R := by rw [hε]; exact J_sub_R π hπ hκE
  have hpow : (1 + ε) ^ (m + 1) = (1 + δ) ^ m := by
    have h3 := congrArg Units.val hκ
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mul, ← hX1, hκ'] at h3
    rw [h3]
    congr 1
    linear_combination (t₂ : K) * h1 - (t₂ : K) * h2 + hB - hδ - (t₂ : K) * hdd
  obtain ⟨p, hp, hp2⟩ := binom2 (m + 1) hεR
  obtain ⟨q, hq, hq2⟩ := binom2 m hδR
  have hE1 : 1 + ((m + 1 : ℕ) : K) * ε + ε ^ 2 * p = 1 + (m : K) * δ + δ ^ 2 * q := by
    rw [← hp2, ← hq2, hpow]
  have ha' : si * ε * p ∈ mulR R ((π : K) ^ 1) := by
    rw [hε]
    obtain ⟨r', hr', hr2⟩ := mem_mulR.1 hκE
    exact mem_mulR.2 ⟨(π : K) ^ k * si * r' * p, R.mul_mem (R.mul_mem hks hr') hp, by
      rw [← hr2]; ring⟩
  obtain ⟨w, hwR, hw⟩ := one_add_unit π hd hn hπ hπ' _ ha'
  obtain ⟨g, hg⟩ : ∃ g : K, g = w * ((m : K) + δ * q) := ⟨_, rfl⟩
  have hgR : g ∈ R := by
    rw [hg]; exact R.mul_mem hwR (R.add_mem (natCast_mem R m) (R.mul_mem hδR hq))
  have hεg : ε = δ * si * g := by
    rw [hg]
    linear_combination (-ε) * hw + w * (si * hE1 - ε * hs)
  have hd1 : X1 - X2 = d := by linear_combination h1 - h2 - hdd
  have hδ2 : δ * X2 = d := by linear_combination X2 * hδ + d * hB
  have hT : ((m + 1 : ℕ) : K) * z * X1 - ((m + 1 : ℕ) : K) * ((κ : K) * z) * X2 - z * d =
      z * d * δ * (si ^ 2 * g ^ 2 * p - q) := by
    have e1 : ((m + 1 : ℕ) : K) * z * X1 - ((m + 1 : ℕ) : K) * ((κ : K) * z) * X2 - z * d =
        z * X2 * ((m : K) * δ - ((m + 1 : ℕ) : K) * ε) := by
      rw [hκ']
      push_cast
      linear_combination ((m : K) + 1) * z * hd1 - (m : K) * z * hδ2
    have e2 : (m : K) * δ - ((m + 1 : ℕ) : K) * ε = ε ^ 2 * p - δ ^ 2 * q := by
      linear_combination -hE1
    rw [e1, e2]
    have e3 : ε ^ 2 = δ ^ 2 * si ^ 2 * g ^ 2 := by rw [hεg]; ring
    rw [e3]
    linear_combination z * δ * (si ^ 2 * g ^ 2 * p - q) * hδ2
  rw [← hX1, ← hX2, ← hdd, hT]
  have hfin : z * d * δ * (si ^ 2 * g ^ 2 * p - q) =
      (π : K) * (((π : K) ^ k * z) * ((π : K) ^ k * d) ^ 2 * ((π : K) ^ k * si) ^ 2 * r * u * g ^ 2 * p) -
      (π : K) ^ (2 * k + 1) * (((π : K) ^ k * z) * ((π : K) ^ k * d) ^ 2 * r * u * q) := by
    rw [hδ3]; ring
  rw [hfin]
  have hZ := hkz z hz
  exact R.sub_mem
    (R.mul_mem hπ (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hZ
      (R.pow_mem hkd 2)) (R.pow_mem hks 2)) hr) huR) (R.pow_mem hgR 2)) hp))
    (R.mul_mem (R.pow_mem hπ _) (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hZ
      (R.pow_mem hkd 2)) hr) huR) hq))
end Formalism.FourierDecayAlt.P
