-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.all_parts_transfer_of_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:25.556261+00:00
-- url     : https://prove2.me/submissions/ea7351e7-d992-4896-af90-b85fb90302f6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_log_le_half
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_cube_mem
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_majAt_zero_right
import Theorems.Thm_Formalism_BranchingDeterminantCap_orthSandwich
import Theorems.Thm_Formalism_BranchingDeterminantCap_transferDeg
import Theorems.Thm_Formalism_BranchingDeterminantCap_transferMuMax
import Theorems.Thm_Formalism_BranchingDeterminantCap_transferPart
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_first_axis_injective
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_inj_y
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_rank
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_fg_cut
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_mem_cut
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_rkK_cut
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_sandwich
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_smul_mem_cut
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_tr_of_core
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement Formalism.HN _root_.Formalism.IndefR.LatticeTransfer.Lat
set_option maxHeartbeats 400000
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution (hE : IdemE) (hP : IdemP) (hC : Core) (hD : DimSq) (hM : Metric) :
    AllPartsTransfer := by
  intro K _ _ _ _ G _ _ S _ T _ _ _ τ H₀ χ₀ H χ hτ hM1 V _ _ _ _ ι _ _ b X ρ hX hU A hA
  obtain ⟨hfg, hspan, hst⟩ := hA
  have : FiniteDimensional K V := Module.Finite.of_basis b
  choose γ δ c Γ hcore using hC K G S T τ H₀ χ₀ H χ hτ hM1
  obtain ⟨he, ho⟩ := hE K G S T τ hτ V ρ
  have tr := fun s => tr_of_core hP (hcore s) ρ (he s)
  obtain ⟨hsa, hnorm⟩ := hM K G V ι b X ρ hX hU
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have hla : 0 ≤ Real.log (Fintype.card G : ℝ) := Real.log_natCast_nonneg _
  have horth : ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) s t, s ≠ t →
      Formalism.BranchingDeterminantCap.OrthAt b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) (cut A (epP H χ ρ ∘ₗ eS (τ t) ρ)) := by
    intro H χ s t hst' v x hx y hy
    have sw := (sandwich hE hP hτ ρ hst H χ).2.2
    rw [← sw s x hx, hsa, ← sw t y hy]
    have : eS (τ s) ρ (eS (τ t) ρ y) = 0 := LinearMap.congr_fun (ho s t hst') y
    rw [this]
    exact Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_zero_right b X v x
  have sw1 := sandwich hE hP hτ ρ hst H χ
  have sw0 := sandwich hE hP hτ ρ hst H₀ χ₀
  have os1 := Formalism.BranchingDeterminantCap.orthSandwich K V ι b X hX S (fun s => cut A (epP H χ ρ ∘ₗ eS (τ s) ρ))
    (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fg_cut hfg _) hN (horth H χ) sw1.1 sw1.2.1
  have os0 := Formalism.BranchingDeterminantCap.orthSandwich K V ι b X hX S (fun s => cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))
    (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fg_cut hfg _) hN (horth H₀ χ₀) sw0.1
    sw0.2.1
  have hrk : ∀ s, rkK (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) =
      nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := fun s => by
    rw [rkK_cut hspan, rkK_cut hspan]; exact (tr s).rank
  have hxm : ∀ s j, ∀ a ∈ cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ),
      ((Fintype.card G : 𝓞 K) ^ 3) • (epP H χ ρ ∘ₗ ρ (γ s j)) a ∈
        cut A (epP H χ ρ ∘ₗ eS (τ s) ρ) := fun s j a ha =>
    cube_mem (smul_mem_cut hP ρ hst H χ _ (tr s).2.1 ha.1
      ((tr s).2.2.1 j a ((mem_cut (tr s).1).1 ha).2))
  have hym : ∀ s i, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ),
      ((Fintype.card G : 𝓞 K) ^ 3) • (epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) a ∈
        cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) := fun s i a ha =>
    cube_mem (smul_mem_cut hP ρ hst H₀ χ₀ _ (tr s).1 ha.1
      ((tr s).2.2.2.1 i a ((mem_cut (tr s).2.1).1 ha).2))
  have hyi : ∀ s, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ),
      (∀ i, (epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) a = 0) → a = 0 := fun s a ha h0 =>
    (tr s).inj_y a ((mem_cut (tr s).2.1).1 ha).2 h0
  have hrk0 : rkK (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) =
      ∑ s, nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := by
    rw [os1.1]; exact Finset.sum_congr rfl fun s _ => hrk s
  have h3a : ∀ s, |degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) -
      (nS (τ s) H χ : ℝ) * degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))| ≤
      (6 * Real.log (Fintype.card G) + Real.log (nS (τ s) H χ)) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) := by
    intro s
    by_cases hn : nS (τ s) H χ = 0
    · simp [degT, hrk s, hn]
    by_cases hr : cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) = ⊥
    · have h0 : rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) = 0 := by
        rw [hr]; simp [rkK]
      simp [degT, hrk s, h0]
    exact Formalism.BranchingDeterminantCap.transferPart K V ι b X hX _ _ _ (Fintype.card G)
      (fun j => epP H χ ρ ∘ₗ ρ (γ s j)) (fun i => epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) (fg_cut hfg _)
      (fg_cut hfg _) hr (Nat.pos_of_ne_zero hn) hN (hxm s) (hym s) (fun i v => hnorm H χ _ v)
      (fun i v => hnorm H₀ χ₀ _ v)
      (fun a ha h0 => (tr s).first_axis_injective a (fun j => ((mem_cut (tr s).1).1 (ha j)).2) h0) (hyi s) (hrk s)
  have h3b : ∀ s, (6 * Real.log (Fintype.card G) + Real.log (nS (τ s) H χ)) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) ≤
      6.5 * Real.log (Fintype.card G) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) := by
    intro s
    have := log_le_half ((hD K G S T τ hτ s).2 H χ)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hcast : ((∑ s, nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) : ℕ) : ℝ) =
      ∑ s, (nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := by push_cast; rfl
  have o12 : ∑ s, degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) ≤
      degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) := os1.2.1
  have o13 : degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) ≤
      ∑ s, degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) + 2 * Real.log (Fintype.card G) *
        (rkK (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) : ℝ) := os1.2.2
  have o02 : ∑ s, degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) ≤
      degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) := os0.2.1
  have o03 : degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) ≤
      ∑ s, degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) + 2 * Real.log (Fintype.card G) *
        (rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) : ℝ) := os0.2.2
  rw [hrk0] at o13
  rw [os0.1, Nat.cast_sum] at o03
  have h4 := Formalism.BranchingDeterminantCap.transferDeg S (fun s => (rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) : ℝ))
    (fun s => (nS (τ s) H χ : ℝ)) (fun s => degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)))
    (fun s => degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ))) (Real.log (Fintype.card G))
    (degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)))
    (fun s => ((h3a s).trans (h3b s)).trans (le_of_eq (by norm_num))) o12 (by rw [← hcast]; exact o13)
    hla (fun s => by positivity)
  have h810 : 8.5 * Real.log (Fintype.card G : ℝ) ≤ 10 * Real.log (Fintype.card G : ℝ) := by
    linarith only [hla]
  have h85 : (17 / 2 : ℝ) = 8.5 := by norm_num
  rw [h85, ← hcast] at h4
  refine ⟨⟨hrk, hrk0⟩, ⟨iSup_le sw1.1, sw1.2.1, fun s t hst' x hx y hy v => horth H χ s t hst' v x hx y hy,
    sub_nonneg.2 o12, sub_le_iff_le_add'.2 o13, sub_nonneg.2 o02, sub_le_iff_le_add'.2 o03⟩,
    fun s => ⟨h3a s, h3b s⟩, ⟨?_, ?_⟩, fun h0 => ⟨?_, add_le_add_right h810 _⟩⟩
  · exact h4
  · exact mul_le_mul_of_nonneg_right h810 (Nat.cast_nonneg _)
  · have := Formalism.BranchingDeterminantCap.transferMuMax K V ι b X hX S (fun s => cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))
      (fun s => cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) (cut A (epP H χ ρ ∘ₗ eGood τ ρ))
      (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fun s => nS (τ s) H χ)
      (fun s i => epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) (fg_cut hfg _) (fg_cut hfg _) h0 hN
      (fun s => (hD K G S T τ hτ s).2 H χ) (horth H χ) sw1.1 sw1.2.1 sw0.1 hym
      (fun s i v => hnorm H₀ χ₀ _ v) hyi
    rw [h85] at this
    exact this
end Formalism.IndefR.LatticeTransfer
