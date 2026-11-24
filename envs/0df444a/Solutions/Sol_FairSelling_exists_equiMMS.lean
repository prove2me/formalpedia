-- Prove2me | solution 1 for FairSelling.exists_equiMMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:09:46.615738+00:00
-- url     : https://prove2.me/submissions/ed6f64da-0ed8-4cd0-bd85-cd00738337fa

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Theorems.Thm_FairSelling_exists_value_reduction
import Theorems.Thm_FairSelling_MMS_liquid_le
import Theorems.Thm_FairSelling_MMSset_bddAbove_of
import Theorems.Thm_FairSelling_exists_MMS_partition
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ w : G → ℝ, (∀ g, 0 ≤ w g) ∧ (∀ g, w g ≤ v g) ∧ MMS n w p = MMS n v p ∧
      Nonempty (EquiMMS w p (MMS n w p) n) := by
  classical
  set μ : ℝ := MMS n v p with hμ
  obtain ⟨o, hovalid, hcover, hoge⟩ := exists_MMS_partition hn v p hv hp
  -- distribute the unspent proceeds, so that the money of the parts is exactly the proceeds
  set slack : ℝ := (∑ g ∈ o.sold, p g) - ∑ l, o.money l with hslack
  have hslack0 : 0 ≤ slack := by rw [hslack]; linarith [hovalid.2.2.2]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set cash : Fin n → ℝ := fun l => o.money l + slack / n with hcash
  have hcash0 : ∀ l, 0 ≤ cash l :=
    fun l => add_nonneg (hovalid.2.2.1 l) (div_nonneg hslack0 (le_of_lt hn'))
  have hcashsum : ∑ l, cash l = ∑ g ∈ o.sold, p g := by
    rw [hcash]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hns : (n : ℝ) * (slack / n) = slack := by field_simp
    rw [hns, hslack]
    ring
  set o2 : Outcome G n := { sold := o.sold, kept := o.kept, money := cash } with ho2
  have ho2valid : o2.Valid p :=
    ⟨hovalid.1, hovalid.2.1, hcash0, le_of_eq hcashsum⟩
  have ho2ge : ∀ l, μ ≤ util v o2 l := by
    intro l
    have h1 := hoge l
    simp only [util, ho2, hcash]
    simp only [util] at h1
    have : 0 ≤ slack / n := div_nonneg hslack0 (le_of_lt hn')
    linarith
  -- the liquid value of every part is at most `μ`
  have hliq : ∀ l, (∑ g ∈ o.kept l, p g) + cash l ≤ μ := by
    intro l
    have := MMS_liquid_le hn v p hv hp ho2valid ho2ge l
    simpa [ho2] using this
  -- and the `v̄`-value of every part is at least `μ`
  have hupper : ∀ l, μ - cash l ≤ ∑ g ∈ o.kept l, max (p g) (v g) := by
    intro l
    have h1 := ho2ge l
    simp only [util, ho2] at h1
    have h2 : ∑ g ∈ o.kept l, v g ≤ ∑ g ∈ o.kept l, max (p g) (v g) :=
      Finset.sum_le_sum (fun g _ => le_max_right _ _)
    linarith
  -- lower the valuation on each part so that the part is worth exactly `μ`
  choose W hW0 hWv hWout hWsum using fun l =>
    exists_value_reduction p hp v hv (o.kept l) (μ - cash l) (by linarith [hliq l]) (hupper l)
  set w : G → ℝ := fun g => if h : ∃ l, g ∈ o.kept l then W h.choose g else min (v g) (p g)
    with hw
  have hkept : ∀ l, ∀ g ∈ o.kept l, w g = W l g := by
    intro l g hg
    have hex : ∃ l, g ∈ o.kept l := ⟨l, hg⟩
    have hcl : hex.choose = l := by
      by_contra hne
      exact Finset.disjoint_left.mp (hovalid.2.1 _ _ hne) hex.choose_spec hg
    simp only [hw, dif_pos hex, hcl]
  have hnotkept : ∀ g, (¬ ∃ l, g ∈ o.kept l) → w g = min (v g) (p g) := by
    intro g hg; simp only [hw, dif_neg hg]
  have hw0 : ∀ g, 0 ≤ w g := by
    intro g
    by_cases hg : ∃ l, g ∈ o.kept l
    · obtain ⟨l, hl⟩ := hg
      rw [hkept l g hl]; exact hW0 l g
    · rw [hnotkept g hg]; exact le_min (hv g) (hp g)
  have hwv : ∀ g, w g ≤ v g := by
    intro g
    by_cases hg : ∃ l, g ∈ o.kept l
    · obtain ⟨l, hl⟩ := hg
      rw [hkept l g hl]; exact hWv l g
    · rw [hnotkept g hg]; exact min_le_left _ _
  have hsoldw : ∀ e ∈ o.sold, w e ≤ p e := by
    intro e he
    have hnot : ¬ ∃ l, e ∈ o.kept l := by
      rintro ⟨l, hl⟩
      exact Finset.disjoint_left.mp (hovalid.1 l) he hl
    rw [hnotkept e hnot]
    exact min_le_right _ _
  have hvalue : ∀ l, vbarSum w p (o.kept l) + cash l = μ := by
    intro l
    have : vbarSum w p (o.kept l) = ∑ g ∈ o.kept l, max (p g) (W l g) := by
      simp only [vbarSum, vbar]
      exact Finset.sum_congr rfl (fun g hg => by rw [hkept l g hg])
    rw [this, hWsum l]
    ring
  -- the maximin share is unchanged
  have hMMSle : MMS n w p ≤ μ := by
    refine csSup_le ⟨0, ?_⟩ ?_
    · exact ⟨{ sold := ∅, kept := fun _ => ∅, money := fun _ => 0 },
        ⟨fun _ => by simp, fun _ _ _ => by simp, fun _ => le_refl 0, by simp⟩,
        fun _ => by simp [util]⟩
    · rintro r ⟨o', ho'valid, ho'ge⟩
      refine le_csSup (MMSset_bddAbove_of hn v p hv hp) ⟨o', ho'valid, fun l => ?_⟩
      refine (ho'ge l).trans ?_
      simp only [util]
      have : ∑ g ∈ o'.kept l, w g ≤ ∑ g ∈ o'.kept l, v g :=
        Finset.sum_le_sum (fun g _ => hwv g)
      linarith
  have hMMSge : μ ≤ MMS n w p := by
    refine le_csSup (MMSset_bddAbove_of hn w p hw0 hp) ?_
    refine ⟨unifiedOutcome (fun _ => w) p o.kept o.sold cash, ?_, fun l => ?_⟩
    · exact unifiedOutcome_valid (fun _ => w) p hp o.kept o.sold cash hovalid.2.1 hovalid.1
        hcash0 (le_of_eq hcashsum)
    · have hu : util w (unifiedOutcome (fun _ => w) p o.kept o.sold cash) l
          = vbarSum w p (o.kept l) + cash l :=
        util_unifiedOutcome (fun _ => w) p o.kept o.sold cash l
      rw [hu, hvalue l]
  have hMMSeq : MMS n w p = μ := le_antisymm hMMSle hMMSge
  refine ⟨w, hw0, hwv, hMMSeq, ⟨o.kept, o.sold, cash, hovalid.2.1, hovalid.1, hcash0,
    hcashsum, ?_, hsoldw⟩⟩
  intro l
  rw [hMMSeq]
  exact hvalue l
end FairSelling
