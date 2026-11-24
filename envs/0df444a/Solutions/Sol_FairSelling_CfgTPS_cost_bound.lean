-- Prove2me | solution 1 for FairSelling.CfgTPS.cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:39.757944+00:00
-- url     : https://prove2.me/submissions/14bee72d-b5f5-4ad8-b981-ca7f6dbfe0d1

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
import Theorems.Thm_FairSelling_CfgTPS_Qc_nonneg
import Theorems.Thm_FairSelling_CfgTPS_Qc_safe
import Theorems.Thm_FairSelling_CfgTPS_not_adm_keep_all
import Theorems.Thm_FairSelling_CfgTPS_saleLoss_le_vbar
import Theorems.Thm_FairSelling_CfgTPS_Qc_empty_le
import Theorems.Thm_FairSelling_CfgTPS_truncBundle_add_le_two
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_cash_add_saleLoss_le
import Theorems.Thm_FairSelling_ChargeTPS_saleLoss_nonneg
import Theorems.Thm_FairSelling_ChargeTPS_sum_saleLoss
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_trunc_le_max
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
    (hp : ∀ g, 0 ≤ p g) (hD : 0 ≤ D)
    (hreq0 : ∀ m, 0 ≤ req m) (hreqt : req j ≤ t j) (htreq : t j ≤ 2 * req j)
    (hUP : S ∪ S₀ ⊆ P) (hdisj : Disjoint S S₀) (hadm : Adm w p req k0 D S S₀)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card) :
    truncBundle (w j) p (t j) S + Qc w p req k0 S
      + ∑ g ∈ S₀, ChargeTPS.saleLoss (w j) p (t j) g ≤ 2 * req j := by
  classical
  have hcosteq : truncBundle (w j) p (t j) S + Qc w p req k0 S
      + ∑ g ∈ S₀, ChargeTPS.saleLoss (w j) p (t j) g
      = truncBundle (w j) p (t j) (S ∪ S₀) + Qc w p req k0 S - ∑ g ∈ S₀, p g := by
    rw [ChargeTPS.sum_saleLoss, truncBundle, truncBundle, truncBundle,
      Finset.sum_union hdisj]
    ring
  have hreqj : 0 ≤ req j := hreq0 j
  rcases lt_or_ge (S ∪ S₀).card 2 with hlt | hge
  · -- the footprint has at most one good
    have hc2 : (S ∪ S₀).card = 0 ∨ (S ∪ S₀).card = 1 := by omega
    rcases hc2 with hc | hc
    · -- empty footprint
      have hSe : S = ∅ := by
        have : S ⊆ S ∪ S₀ := Finset.subset_union_left
        rw [Finset.card_eq_zero.mp hc] at this
        exact Finset.subset_empty.mp this
      have hS₀e : S₀ = ∅ := by
        have : S₀ ⊆ S ∪ S₀ := Finset.subset_union_right
        rw [Finset.card_eq_zero.mp hc] at this
        exact Finset.subset_empty.mp this
      rw [hSe, hS₀e]
      simp only [truncBundle, Finset.sum_empty, zero_add, add_zero]
      linarith [Qc_empty_le (w := w) (p := p) (k0 := k0) hreq0 j]
    · -- one good in the footprint
      obtain ⟨g, hgU⟩ := Finset.card_eq_one.mp hc
      have hScases : S = ∅ ∨ S = {g} :=
        Finset.subset_singleton_iff.mp (hgU ▸ (Finset.subset_union_left : S ⊆ S ∪ S₀))
      have hS₀cases : S₀ = ∅ ∨ S₀ = {g} :=
        Finset.subset_singleton_iff.mp (hgU ▸ (Finset.subset_union_right : S₀ ⊆ S ∪ S₀))
      have hQ1nn : 0 ≤ Qc w p req k0 ({g} : Finset G) := Qc_nonneg w p req k0 _
      rcases hScases with hSe | hSe
      · -- the good is sold
        rcases hS₀cases with hS₀e | hS₀e
        · exfalso; rw [hSe, hS₀e] at hgU; simp at hgU
        · -- `S = ∅`, `S₀ = {g}`
          rw [hSe, hS₀e]
          simp only [truncBundle, Finset.sum_empty, zero_add, Finset.sum_singleton]
          have hRle : ∀ m, Qc w p req k0 (∅ : Finset G) ≤ req m := fun m => Qc_empty_le hreq0 m
          have hloss := saleLoss_le_vbar (p := p) (t j) (w j) g
          have hloss0 := ChargeTPS.saleLoss_nonneg (w j) p (t j) g
          have hnotadm : ¬ Adm w p req k0 D (S ∪ S₀) ∅ :=
            not_adm_keep_all hUP hmin (by rw [hS₀e]; exact ⟨g, by simp⟩)
          rw [hgU] at hnotadm
          by_cases hfeasg : Feas w p req k0 D ({g} : Finset G) ∅
          · -- keeping the good is feasible, so it must be inadmissible
            have hviol : ∃ X ⊆ ({g} : Finset G), X.Nonempty ∧ ∃ m,
                req m < vbarSum (w m) p (({g} : Finset G) \ X) + (∑ x ∈ X, p x)
                  + Qc w p req k0 ({g} : Finset G) := by
              by_contra hcon
              push_neg at hcon
              exact hnotadm ⟨hfeasg, fun X hX hXne m => hcon X hX hXne m⟩
            obtain ⟨X, hX, hXne, m, hm⟩ := hviol
            have hXg : X = {g} := (Finset.subset_singleton_iff.mp hX).resolve_left
              (Finset.nonempty_iff_ne_empty.mp hXne)
            rw [hXg] at hm
            simp only [Finset.sdiff_self, vbarSum, Finset.sum_empty, zero_add,
              Finset.sum_singleton] at hm
            rcases eq_or_lt_of_le hQ1nn with hQ1 | hQ1
            · -- the good alone needs no cash: its price exceeds every requirement
              have hRp : Qc w p req k0 (∅ : Finset G) ≤ p g := by
                linarith [hRle m]
              have hRt : Qc w p req k0 (∅ : Finset G) ≤ t j := le_trans (hRle j) hreqt
              have := ChargeTPS.cash_add_saleLoss_le (w j) p (t j) g
                (Qc w p req k0 (∅ : Finset G)) hRp hRt
              linarith
            · -- the good alone needs cash, and then nobody envies it
              have hsafe := Qc_safe w p req k0 hQ1 j
              simp only [vbarSum, Finset.sum_singleton] at hsafe
              linarith [hRle m]
          · -- keeping the good is infeasible
            have hQ1D : D < Qc w p req k0 ({g} : Finset G) := by
              unfold Feas at hfeasg
              push_neg at hfeasg
              simpa using hfeasg
            have hQ1pos : 0 < Qc w p req k0 ({g} : Finset G) := lt_of_le_of_lt hD hQ1D
            have hsafe := Qc_safe w p req k0 hQ1pos j
            simp only [vbarSum, Finset.sum_singleton] at hsafe
            linarith [hRle j, hp g]
      · -- the good is kept
        rcases hS₀cases with hS₀e | hS₀e
        · rw [hSe, hS₀e]
          simp only [truncBundle, Finset.sum_singleton, Finset.sum_empty, add_zero]
          rcases eq_or_lt_of_le hQ1nn with hQ1 | hQ1
          · -- no cash: the good's price is bounded by the requirement
            have hpg : p g ≤ req j := by
              have := hadm.2 {g} (by rw [hSe]) ⟨g, by simp⟩ j
              rw [hSe] at this
              simp only [Finset.sdiff_self, vbarSum, Finset.sum_empty, zero_add,
                Finset.sum_singleton] at this
              linarith
            have h1 : trunc (w j) p (t j) g ≤ max (p g) (t j) := trunc_le_max _ _ _ _
            rcases max_cases (p g) (t j) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h1 <;>
              linarith
          · have hsafe := Qc_safe w p req k0 hQ1 j
            simp only [vbarSum, Finset.sum_singleton] at hsafe
            have := trunc_le_vbar (w j) p (t j) g
            linarith
        · exfalso; rw [hSe, hS₀e] at hdisj; simp at hdisj
  · -- the footprint has at least two goods
    have h1 := truncBundle_add_le_two (w := w) (req := req) (k0 := k0) t j hp hD hUP hmin hge
    have h2 := hadm.1
    unfold Feas at h2
    rw [hcosteq]
    linarith
end FairSelling.CfgTPS
