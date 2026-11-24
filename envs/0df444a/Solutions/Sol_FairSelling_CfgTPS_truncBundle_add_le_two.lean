-- Prove2me | solution 1 for FairSelling.CfgTPS.truncBundle_add_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:08.455829+00:00
-- url     : https://prove2.me/submissions/efa98bac-2a0d-4835-97ba-7f81cfb4837c

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
import Theorems.Thm_FairSelling_CfgTPS_gapMin_le
import Theorems.Thm_FairSelling_CfgTPS_lt_Qc_erase
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_truncBundle_le_vbarSum
import Theorems.Thm_FairSelling_truncBundle_sdiff
import Theorems.Thm_FairSelling_trunc_le_vbar
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w : Fin n → G → ℝ} {p : G → ℝ} {req : Fin n → ℝ} {k0 : Fin n} {D : ℝ}
omit [Fintype G]
namespace FairSelling.CfgTPS
theorem _root_.solution {P S S₀ : Finset G} (t : Fin n → ℝ) (j : Fin n)
    (hp : ∀ g, 0 ≤ p g) (hD : 0 ≤ D) (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    (hcard : 2 ≤ (S ∪ S₀).card) :
    truncBundle (w j) p (t j) (S ∪ S₀) + D ≤ 2 * req j := by
  classical
  set U := S ∪ S₀ with hU
  obtain ⟨g, hg, h, hh, hgh⟩ := Finset.one_lt_card.mp hcard
  have key : ∀ x ∈ U, vbarSum (w j) p (U \ {x}) < req j - D := by
    intro x hx
    have h1 : D < Qc w p req k0 (U \ {x}) := lt_Qc_erase hp hUP hmin hx
    have h2 : D < gapMin w p req k0 (U \ {x}) := by
      unfold Qc at h1
      rcases max_cases (0:ℝ) (gapMin w p req k0 (U \ {x})) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at h1; linarith
      · rw [he] at h1; exact h1
    have h3 := gapMin_le w p req k0 (U \ {x}) j
    linarith
  have hsplit : truncBundle (w j) p (t j) U
      = truncBundle (w j) p (t j) (U \ {g}) + truncBundle (w j) p (t j) ({g} : Finset G) :=
    truncBundle_sdiff (w j) p (t j) (Finset.singleton_subset_iff.mpr hg)
  have h1 : truncBundle (w j) p (t j) (U \ {g}) ≤ vbarSum (w j) p (U \ {g}) :=
    truncBundle_le_vbarSum _ _ _ _
  have hgU : g ∈ U \ {h} := Finset.mem_sdiff.mpr ⟨hg, by simpa using hgh⟩
  have h2 : truncBundle (w j) p (t j) ({g} : Finset G) ≤ vbarSum (w j) p (U \ {h}) := by
    simp only [truncBundle, Finset.sum_singleton]
    refine le_trans (trunc_le_vbar (w j) p (t j) g) ?_
    refine Finset.single_le_sum (fun x _ => ?_) hgU
    exact le_trans (hp x) (le_max_left _ _)
  have k1 := key g hg
  have k2 := key h hh
  linarith
end FairSelling.CfgTPS
