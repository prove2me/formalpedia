-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:46.16137+00:00
-- url     : https://prove2.me/submissions/3426d7f7-db6f-43a5-a473-84b6b024e6f8

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_lp_add
import Theorems.Thm_Formalism_G0_WalkSharpP_lp_zero
import Theorems.Thm_Formalism_G0_WalkSharpP_lp_finRange_single
import Theorems.Thm_Formalism_G0_WalkSharpP_lp_mem
import Theorems.Thm_Formalism_G0_WalkSharpP_monoOp_eq
import Theorems.Thm_Formalism_G0_WalkSharpP_le_top
import Theorems.Thm_Formalism_G0_WalkSharpP_top_mem
import Theorems.Thm_Formalism_G0_WalkSharpP_update_positionAt_dual
import Theorems.Thm_Formalism_G0_WalkSharpP_update_positionAt_base
import Theorems.Thm_Formalism_G0_WalkSharpP_update_positionAt_dual_self
import Theorems.Thm_Formalism_G0_WalkSharpP_update_positionAt_base_self
import Theorems.Thm_Formalism_G0_WalkSharpP_L_sideAt_le
import Theorems.Thm_Formalism_G0_WalkSharpP_enter_positionAt
import Theorems.Thm_Formalism_G0_WalkSharpP_mem_idx
import Theorems.Thm_Formalism_G0_WalkSharpP_card_idx
import Theorems.Thm_Formalism_G0_WalkSharpP_expo_step
import Theorems.Thm_Formalism_G0_WalkSharpP_accT_step
import Theorems.Thm_Formalism_G0_WalkSharpP_expo_move
import Theorems.Thm_Formalism_G0_WalkSharpP_accT_move
import Theorems.Thm_Formalism_G0_WalkSharpP_accT_le
import Theorems.Thm_Formalism_G0_WalkSharpP_walkCostTerm_add_le
import Theorems.Thm_Formalism_G0_WalkSharpP_accT_stop_le
import Theorems.Thm_Formalism_G0_WalkSharpP_sum_add_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
set_option maxHeartbeats 4000000
namespace Formalism.G0.WalkSharpP
theorem _root_.solution : WalkSharp := by

  intro R X _ _ _ V π L y m β c₀ S a b c Sv g G hm hc hbb hdb ha hb hcb hy hG hS
  classical
  unfold AllButLE
  have hupd : ∀ u : Fin V, Function.update (fun _ : Fin V => Slot.base) u Slot.base =
      fun _ => Slot.base := by
    intro u
    funext w
    by_cases h : w = u
    · subst h
      simp
    · simp [Function.update_apply, h]
  have hyM : ∀ u, ∀ x ∈ L (fun _ => Slot.base), y u x ∈ L (fun _ => Slot.base) := by
    intro u x hx
    have h1 : x ∈ L (Function.update (fun _ => Slot.base) u Slot.base) := by
      rw [hupd]
      exact hx
    have h2 := hdb _ u (hy _ u x (hbb _ u h1))
    rw [hupd] at h2
    exact h2
  have hPmem : ∀ (e : Fin V → Bool), ∀ x ∈ L (fun _ => Slot.base),
      monoOp π y m Sv e x ∈ prodIdealMap π y m Sv (L fun _ => Slot.base) := by
    intro e x hx
    unfold prodIdealMap
    exact Submodule.mem_iSup_of_mem e (Submodule.mem_map_of_mem hx)
  have hP2 : ∀ x ∈ L (fun _ => Slot.base),
      π ^ (∑ v, Sv v) • x ∈ prodIdealMap π y m Sv (L fun _ => Slot.base) := by
    intro x hx
    have h2 := hPmem (fun _ => false) x hx
    rw [monoOp_eq] at h2
    simpa [lp_zero] using h2
  refine ⟨?_, ⟨∅, by simp, by simp, fun x hx => Submodule.mem_sup_left (hP2 x hx)⟩⟩
  by_cases hV : β + 1 ≤ V
  swap
  · refine ⟨∅, by simp, by simp, fun x hx => Submodule.mem_sup_left ?_⟩
    have hle : ∑ v, Sv v ≤ ∑ v, (a v + b v + (m - 1) * c v + m * c₀) + β * S := by
      have h1 : ∑ v, Sv v ≤ ∑ _v : Fin V, S := Finset.sum_le_sum fun v _ => hS v
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
      have h2 : V * S ≤ β * S := Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hP2 x hx)
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ v, (a v + b v + (m - 1) * c v + m * c₀) + β * S := ⟨_, rfl⟩
  rw [← hE]
  obtain ⟨C, hC⟩ : ∃ C : Finset X, C = (Finset.univ.powersetCard (β + 1)).biUnion fun B =>
      (idx m B).biUnion fun i => (G B).image (lp y (List.finRange V) (expo m B i)) := ⟨_, rfl⟩
  have hstateC : ∀ B : Finset (Fin V), B.card = β + 1 → ∀ i ∈ idx m B, ∀ x ∈ G B,
      lp y (List.finRange V) (expo m B i) x ∈ C := by
    intro B hB i hi x hx
    rw [hC, Finset.mem_biUnion]
    refine ⟨B, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ B, hB⟩, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨i, hi, Finset.mem_image_of_mem _ hx⟩
  have hCsub : (↑C : Set X) ⊆ L (fun _ => Slot.base) := by
    intro x hx
    rw [Finset.mem_coe, hC] at hx
    simp only [Finset.mem_biUnion, Finset.mem_image] at hx
    obtain ⟨B, hBm, i, _, g0, hg0, rfl⟩ := hx
    have hB' := (Finset.mem_powersetCard.mp hBm).2
    exact lp_mem y _ hyM _ _ g0 (L_sideAt_le L hdb B ((hG B hB').1 hg0))
  have hCcard : C.card ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1), m ^ (β + 1) * g B := by
    rw [hC]
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun B hB => ?_)
    have hB' := (Finset.mem_powersetCard.mp hB).2
    refine Finset.card_biUnion_le.trans ?_
    refine le_trans (Finset.sum_le_sum fun i _ => Finset.card_image_le) ?_
    rw [Finset.sum_const, card_idx, hB', smul_eq_mul]
    exact Nat.mul_le_mul_left _ (hG B hB').2.1
  refine ⟨C, hCsub, hCcard, ?_⟩
  have hbnd : ∀ (B : Finset (Fin V)) (i : Fin V → ℕ), (∀ u ∈ B, i u < m) →
      acc a b c m c₀ B i ≤ ∑ u, (a u + b u + (m - 1) * c u + m * c₀) := by
    intro B i hi
    unfold acc
    exact Finset.sum_le_sum fun u _ => accT_le a b c m c₀ hi u
  have hexpo_le : ∀ (B : Finset (Fin V)) (i : Fin V → ℕ), i ∈ idx m B → ∀ u, expo m B i u ≤ m := by
    intro B i hi u
    have := (mem_idx.mp hi u).1
    unfold expo
    split_ifs with h1 h2
    · exact le_rfl
    · exact (this h2).le
    · exact Nat.zero_le _
  have hsumexpo : ∀ (B : Finset (Fin V)) (i : Fin V → ℕ), i ∈ idx m B → ∑ u, expo m B i u ≤ m * V := by
    intro B i hi
    calc ∑ u, expo m B i u ≤ ∑ _u : Fin V, m := Finset.sum_le_sum fun u _ => hexpo_le B i hi u
      _ = m * V := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
  have claim : ∀ n : ℕ, ∀ (B : Finset (Fin V)) (i : Fin V → ℕ), B.card = β + 1 → i ∈ idx m B →
      m * V + 1 ≤ (∑ u, expo m B i u) + n → ∀ z ∈ L (vertexLabel B),
      π ^ (E - acc a b c m c₀ B i) • lp y (List.finRange V) (expo m B i) z ∈
        prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X) := by
    intro n
    induction n with
    | zero =>
      intro B i _ hi hn
      have := hsumexpo B i hi
      exfalso
      omega
    | succ n ih =>
      intro B i hB hi hn z hz
      obtain ⟨-, -, hdec⟩ := hG B hB
      have hi' : ∀ u ∈ B, i u < m := fun u hu => (mem_idx.mp hi u).1 hu
      have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨t, ht⟩ := hBne
      have hacc : acc a b c m c₀ B i + c₀ ≤ E := by
        have h1 : acc a b c m c₀ B i + c₀ =
            ∑ u, (accT a b c m c₀ B i u + if u = t then c₀ else 0) := by
          rw [sum_add_ite]
          rfl
        have h2 : ∑ u, (accT a b c m c₀ B i u + if u = t then c₀ else 0) ≤
            ∑ u, (a u + b u + (m - 1) * c u + m * c₀) :=
          Finset.sum_le_sum fun u _ => walkCostTerm_add_le a b c m c₀ hi' ht u
        rw [hE]
        omega
      obtain ⟨k, hk⟩ : ∃ k, E - acc a b c m c₀ B i = k + c₀ :=
        ⟨E - acc a b c m c₀ B i - c₀, by omega⟩
      obtain ⟨Y, hY⟩ : ∃ Y, Y = lp y (List.finRange V) (expo m B i) := ⟨_, rfl⟩
      rw [← hY]
      have hstep : ∀ v ∈ B, ∀ zv ∈ L (Function.update (vertexLabel B) v Slot.ball),
          π ^ k • Y (y v zv) ∈
            prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X) := by
        intro v hv zv hzv
        have hYy : ∀ e₂ : Fin V → ℕ, (∀ u, e₂ u = expo m B i u + if u = v then 1 else 0) →
            lp y (List.finRange V) e₂ = Y * y v := by
          intro e₂ he
          rw [show e₂ = _ from funext he, lp_add y hc, lp_finRange_single, hY]
        by_cases hlt : i v + 1 < m
        · have hi2 : Function.update i v (i v + 1) ∈ idx m B := by
            rw [mem_idx]
            intro u
            by_cases huv : u = v
            · subst u
              refine ⟨fun _ => ?_, fun h => absurd hv h⟩
              rw [Function.update_apply, if_pos rfl]
              exact hlt
            · rw [Function.update_apply, if_neg huv]
              exact mem_idx.mp hi u
          have hz2 : π ^ c v • zv ∈ L (vertexLabel B) := by
            have := hcb _ v zv hzv
            rwa [update_positionAt_dual_self hv] at this
          have hmu : ∑ u, expo m B (Function.update i v (i v + 1)) u = (∑ u, expo m B i u) + 1 := by
            simp only [expo_step m i hv, sum_add_ite]
          have hacc2 : acc a b c m c₀ B (Function.update i v (i v + 1)) =
              acc a b c m c₀ B i + (c v + c₀) := by
            simp only [acc, accT_step a b c m c₀ i hv, sum_add_ite]
          have hle2 : acc a b c m c₀ B (Function.update i v (i v + 1)) ≤ E := by
            have := hbnd B _ (fun u hu => (mem_idx.mp hi2 u).1 hu)
            rw [hE]
            omega
          have IH := ih B _ hB hi2 (by omega) _ hz2
          rw [hYy _ (fun u => expo_step m i hv u), map_smul, smul_smul, ← pow_add] at IH
          have hk2 : E - acc a b c m c₀ B (Function.update i v (i v + 1)) + c v = k := by omega
          rw [hk2] at IH
          exact IH
        have hiv : i v + 1 = m := by
          have := hi' v hv
          omega
        by_cases htop : top B + 1 < V
        · obtain ⟨w, hw⟩ : ∃ w : Fin V, (w : ℕ) = top B + 1 := ⟨⟨top B + 1, htop⟩, rfl⟩
          have hwB : w ∉ B := fun h => by
            have := le_top h
            omega
          have hwB2 : w ∉ B.erase v := fun h => hwB (Finset.mem_of_mem_erase h)
          have hiw : i w = 0 := (mem_idx.mp hi w).2 hwB
          have hB2 : (insert w (B.erase v)).card = β + 1 := by
            rw [Finset.card_insert_eq_ite, if_neg hwB2, Finset.card_erase_of_mem hv, hB]
            omega
          have hi2 : Function.update i v 0 ∈ idx m (insert w (B.erase v)) := by
            rw [mem_idx]
            intro u
            by_cases huv : u = v
            · subst u
              rw [Function.update_apply, if_pos rfl]
              exact ⟨fun _ => by omega, fun _ => rfl⟩
            · rw [Function.update_apply, if_neg huv]
              constructor
              · intro h
                rcases Finset.mem_insert.mp h with h | h
                · rw [h, hiw]
                  omega
                · exact hi' u (Finset.mem_of_mem_erase h)
              · intro h
                have hnB : u ∉ B := fun hu =>
                  h (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨huv, hu⟩))
                exact (mem_idx.mp hi u).2 hnB
          have hz2 : π ^ b w • π ^ a v • zv ∈ L (vertexLabel (insert w (B.erase v))) := by
            have h1 := ha _ v zv hzv
            rw [update_positionAt_base] at h1
            have h2 : π ^ a v • zv ∈ L (Function.update (vertexLabel (B.erase v)) w Slot.base) := by
              rw [update_positionAt_base_self hwB2]
              exact h1
            have h3 := hb _ w _ h2
            rwa [update_positionAt_dual] at h3
          have hmu : ∑ u, expo m (insert w (B.erase v)) (Function.update i v 0) u =
              (∑ u, expo m B i u) + 1 := by
            simp only [expo_move hv hiv hw hiw, sum_add_ite]
          have hacc2 : acc a b c m c₀ (insert w (B.erase v)) (Function.update i v 0) =
              acc a b c m c₀ B i + (a v + c₀) + b w := by
            simp only [acc, accT_move a b c hv hiv hw hiw, sum_add_ite]
          have hle2 : acc a b c m c₀ (insert w (B.erase v)) (Function.update i v 0) ≤ E := by
            have := hbnd _ _ (fun u hu => (mem_idx.mp hi2 u).1 hu)
            rw [hE]
            omega
          have IH := ih _ _ hB2 hi2 (by omega) _ hz2
          rw [hYy _ (fun u => expo_move hv hiv hw hiw u), map_smul, map_smul, smul_smul, smul_smul,
            ← pow_add, ← pow_add] at IH
          have hk2 : E - acc a b c m c₀ (insert w (B.erase v)) (Function.update i v 0) + b w + a v = k := by
            omega
          rw [hk2] at IH
          exact IH
        · have hD : ∀ u, (if decide (u ∉ B.erase v) = true then m else 0) +
              (if u ∈ B.erase v then i u else 0) = expo m B i u + if u = v then 1 else 0 := by
            intro u
            by_cases huv : u = v
            · subst u
              have h1 : ¬((v : ℕ) < top B ∧ v ∉ B) := fun h => h.2 hv
              simp [expo, h1, hv, hiv]
            · by_cases huB : u ∈ B
              · have h1 : ¬((u : ℕ) < top B ∧ u ∉ B) := fun h => h.2 huB
                simp [expo, h1, huB, huv]
              · have hlt2 : (u : ℕ) < top B := by
                  obtain ⟨t', ht', htt⟩ := top_mem ⟨v, hv⟩
                  have h1 : (u : ℕ) ≠ top B := fun h =>
                    huB (by rw [show u = t' from Fin.ext (h.trans htt.symm)]; exact ht')
                  have := u.isLt
                  omega
                simp [expo, hlt2, huB, huv]
          have hprod : lp y (List.finRange V) (fun u => if decide (u ∉ B.erase v) = true then m else 0) *
              lp y (List.finRange V) (fun u => if u ∈ B.erase v then i u else 0) = Y * y v := by
            rw [← lp_add y hc]
            exact hYy _ hD
          have heq : (Y * y v) (π ^ a v • zv) =
              lp y (List.finRange V) (fun u => if decide (u ∉ B.erase v) = true then m else 0)
                (lp y (List.finRange V) (fun u => if u ∈ B.erase v then i u else 0) (π ^ a v • zv)) := by
            rw [← hprod]
            rfl
          have hx' : lp y (List.finRange V) (fun u => if u ∈ B.erase v then i u else 0) (π ^ a v • zv) ∈
              L (fun _ => Slot.base) := by
            apply lp_mem y _ hyM
            have h1 := ha _ v zv hzv
            rw [update_positionAt_base] at h1
            exact L_sideAt_le L hdb _ h1
          have hmono := hPmem (fun u => decide (u ∉ B.erase v)) _ hx'
          rw [monoOp_eq, LinearMap.smul_apply, ← heq, map_smul, smul_smul, ← pow_add] at hmono
          have hs : (∑ u, if decide (u ∉ B.erase v) = true then 0 else Sv u) ≤ β * S := by
            have h1 : (∑ u, if decide (u ∉ B.erase v) = true then 0 else Sv u) = ∑ u ∈ B.erase v, Sv u := by
              symm
              calc ∑ u ∈ B.erase v, Sv u =
                    ∑ u ∈ B.erase v, (if decide (u ∉ B.erase v) = true then 0 else Sv u) :=
                    Finset.sum_congr rfl fun u hu =>
                      (if_neg (by rw [decide_eq_true_eq, not_not]; exact hu)).symm
                _ = ∑ u, (if decide (u ∉ B.erase v) = true then 0 else Sv u) :=
                    Finset.sum_subset (Finset.subset_univ _) fun u _ hu =>
                      if_pos (by rw [decide_eq_true_eq]; exact hu)
            rw [h1]
            calc ∑ u ∈ B.erase v, Sv u ≤ (B.erase v).card • S :=
                  Finset.sum_le_card_nsmul _ _ _ fun u _ => hS u
              _ = β * S := by
                  rw [Finset.card_erase_of_mem hv, hB, smul_eq_mul, Nat.add_sub_cancel]
          have hstop : acc a b c m c₀ B i + (a v + c₀) ≤ ∑ u, (a u + b u + (m - 1) * c u + m * c₀) := by
            have h2 : ∑ u, (accT a b c m c₀ B i u + if u = v then a v + c₀ else 0) ≤
                ∑ u, (a u + b u + (m - 1) * c u + m * c₀) :=
              Finset.sum_le_sum fun u _ => accT_stop_le a b c m c₀ hi' hv hiv u
            rw [sum_add_ite] at h2
            exact h2
          obtain ⟨r, hr⟩ : ∃ r, k = r + ((∑ u, if decide (u ∉ B.erase v) = true then 0 else Sv u) + a v) :=
            ⟨k - ((∑ u, if decide (u ∉ B.erase v) = true then 0 else Sv u) + a v), by omega⟩
          rw [hr, pow_add, mul_smul]
          exact Submodule.mem_sup_left (Submodule.smul_mem _ _ hmono)
      have hle : (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X) ≤
          (prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X)).comap
            (π ^ k • Y) := by
        apply sup_le
        · apply iSup₂_le
          intro v hv
          rw [Submodule.map_le_iff_le_comap]
          intro zv hzv
          rw [Submodule.mem_comap, Submodule.mem_comap, LinearMap.smul_apply]
          exact hstep v hv zv hzv
        · rw [Submodule.span_le]
          intro x hx
          rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, hY]
          exact Submodule.smul_mem _ _
            (Submodule.mem_sup_right (Submodule.subset_span (hstateC B hB i hi x hx)))
      have h := hle (hdec z hz)
      rw [Submodule.mem_comap, LinearMap.smul_apply, map_smul, smul_smul, ← pow_add, ← hk] at h
      exact h
  intro x hx
  obtain ⟨B₀, hB₀card, hB₀⟩ : ∃ B₀ : Finset (Fin V), B₀.card = β + 1 ∧
      ∀ u : Fin V, u ∈ B₀ ↔ (u : ℕ) < β + 1 := by
    refine ⟨Finset.univ.map (Fin.castLEEmb hV), by simp, fun u => ?_⟩
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, rfl⟩
      exact p.isLt
    · intro h
      exact ⟨⟨u, h⟩, Fin.ext rfl⟩
  have hB₀top : top B₀ ≤ β := by
    apply Finset.sup_le
    intro u hu
    have := (hB₀ u).mp hu
    show (u : ℕ) ≤ β
    omega
  have hi0 : (fun _ => 0) ∈ idx m B₀ := by
    rw [mem_idx]
    intro u
    exact ⟨fun _ => show 0 < m by omega, fun _ => rfl⟩
  have hexpo0 : expo m B₀ (fun _ => 0) = fun _ => 0 := by
    funext u
    by_cases hu : u ∈ B₀
    · have h1 : ¬((u : ℕ) < top B₀ ∧ u ∉ B₀) := fun h => h.2 hu
      simp [expo, h1, hu]
    · have h1 : ¬((u : ℕ) < top B₀) := fun h => hu ((hB₀ u).mpr (by omega))
      simp [expo, h1, hu]
  have hacc0 : acc a b c m c₀ B₀ (fun _ => 0) = ∑ u ∈ B₀, b u := by
    have h1 : ∀ u, accT a b c m c₀ B₀ (fun _ => 0) u = if u ∈ B₀ then b u else 0 := by
      intro u
      by_cases hu : u ∈ B₀
      · have h1 : ¬((u : ℕ) < top B₀ ∧ u ∉ B₀) := fun h => h.2 hu
        simp [accT, h1, hu]
      · have h1 : ¬((u : ℕ) < top B₀) := fun h => hu ((hB₀ u).mpr (by omega))
        simp [accT, h1, hu]
    unfold acc
    rw [Finset.sum_congr rfl fun u _ => h1 u]
    symm
    calc ∑ u ∈ B₀, b u = ∑ u ∈ B₀, (if u ∈ B₀ then b u else 0) :=
          Finset.sum_congr rfl fun u hu => (if_pos hu).symm
      _ = ∑ u, (if u ∈ B₀ then b u else 0) :=
          Finset.sum_subset (Finset.subset_univ B₀) fun u _ hu => if_neg hu
  have hle0 : ∑ u ∈ B₀, b u ≤ E := by
    rw [← hacc0, hE]
    have := hbnd B₀ (fun _ => 0) (fun u _ => show 0 < m by omega)
    omega
  have hz0 := enter_positionAt L π b hb B₀ x hx
  have hmain := claim (m * V + 1) B₀ (fun _ => 0) hB₀card hi0 (by omega) _ hz0
  have hone : ∀ w : X, (1 : Module.End R X) w = w := fun _ => rfl
  rw [hexpo0, lp_zero, hacc0, hone, smul_smul, ← pow_add, Nat.sub_add_cancel hle0] at hmain
  exact hmain
end Formalism.G0.WalkSharpP
