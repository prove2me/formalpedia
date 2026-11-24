-- Prove2me | solution 1 for FairSelling.descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:17.462505+00:00
-- url     : https://prove2.me/submissions/136cabe9-de38-4b82-ba9d-afe3bc71dce7

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
import Definitions.Def_RequestProject_TwoThirdsDescent
import Theorems.Thm_FairSelling_cred_bundle_le
import Theorems.Thm_FairSelling_pair_acceptable
import Theorems.Thm_FairSelling_exit_count
import Theorems.Thm_FairSelling_CanonExists_mono
import Theorems.Thm_FairSelling_canonExists_of_nonempty
import Theorems.Thm_FairSelling_canonExists_zero
import Theorems.Thm_FairSelling_canonical_cons
import Theorems.Thm_FairSelling_exists_canonical_of_large_pairs


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε)
    (bg : ι → Finset G) (wit : κ → G) (bidx : κ → ι) (cred : κ → ℝ)
    (Sset : Finset G) (D : ℝ) (hD : 0 ≤ D)
    (hSwp : ∀ g ∈ Sset, w g ≤ p g)
    (hbdisj : ∀ j j', j ≠ j' → Disjoint (bg j) (bg j'))
    (hbS : ∀ j, Disjoint Sset (bg j))
    (hbval : ∀ j, vbarSum w p (bg j) ≤ 3 * ε) :
    ∀ (M : ℕ) (R : Finset G) (J : Finset ι) (Q : Finset κ) (k n₂ : ℕ),
      J.card = M →
      Sset ⊆ R →
      (∀ g ∈ R, vbar w p g ≤ 2 * ε) →
      (∀ b ∈ Q, wit b ∈ bg (bidx b)) →
      (∀ b ∈ Q, cred b ≤ 3 * ε) →
      (∀ b ∈ Q, cred b ≤ vbar w p (wit b) + ε) →
      (∀ b ∈ Q, wit b ∉ R) →
      Set.InjOn wit ↑Q →
      (∀ b ∈ Q, bidx b ∈ J) →
      k + n₂ + Q.card = J.card →
      ((J.card : ℝ) * (3 * ε)
        ≤ (∑ j ∈ J, vbarSum w p (bg j ∩ R)) + (∑ g ∈ Sset, p g) + D
            + (n₂ : ℝ) * (2 * ε) + ∑ b ∈ Q, cred b) →
      CanonExists w p (3 * ε) (2 * ε) k R D := by
  classical
  have hv0 : ∀ g, 0 ≤ vbar w p g := fun g => le_trans (hp g) (le_max_left _ _)
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro R J Q k n₂ hM hSR hsmall hwit_mem hcred_le hcred_wit hwout hinj hbQ hcount hbud
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0; exact canonExists_zero _ _ _ _ _ _
  -- the large goods that are still available and still lie in a surviving bundle
  set Lset : Finset G := (R ∩ J.biUnion bg).filter (fun g => ε ≤ vbar w p g) with hLset
  set Mix : Finset ι := J.filter (fun j => (Q.filter (fun b => bidx b = j)).Nonempty ∧
      (Lset.filter (fun g => g ∈ bg j)).Nonempty) with hMix
  rcases Classical.em (∃ j ∈ J, 2 ≤ (Q.filter (fun b => bidx b = j)).card) with
    hcase1 | hcase1
  · -- **first transformation**: a bundle carrying two witness goods is discarded
    obtain ⟨j, hjJ, hj2⟩ := hcase1
    have hcredj := cred_bundle_le w p hp bg wit bidx cred hwit_mem hcred_wit hbval hwout hinj j
    have hQcard : (Q.filter (fun b => bidx b = j)).card
        + (Q.filter (fun b => ¬ (bidx b = j))).card = Q.card :=
      Finset.card_filter_add_card_filter_not _
    have hsumQ : (∑ b ∈ Q, cred b)
        = (∑ b ∈ Q.filter (fun b => bidx b = j), cred b)
          + ∑ b ∈ Q.filter (fun b => ¬ (bidx b = j)), cred b :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hJcard : (J.erase j).card = J.card - 1 := Finset.card_erase_of_mem hjJ
    have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr ⟨j, hjJ⟩
    have hsumJ : (∑ j' ∈ J, vbarSum w p (bg j' ∩ R))
        = vbarSum w p (bg j ∩ R) + ∑ j' ∈ J.erase j, vbarSum w p (bg j' ∩ R) :=
      (Finset.add_sum_erase _ _ hjJ).symm
    refine ih (J.card - 1) (by omega) R (J.erase j) (Q.filter (fun b => ¬ (bidx b = j))) k
      (n₂ + ((Q.filter (fun b => bidx b = j)).card - 1)) hJcard hSR hsmall
      (fun b hb => hwit_mem b (Finset.mem_filter.mp hb).1)
      (fun b hb => hcred_le b (Finset.mem_filter.mp hb).1)
      (fun b hb => hcred_wit b (Finset.mem_filter.mp hb).1)
      (fun b hb => hwout b (Finset.mem_filter.mp hb).1)
      (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))
      (fun b hb => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hb).2,
        hbQ b (Finset.mem_filter.mp hb).1⟩)
      (by rw [hJcard]; omega) ?_
    have hc1 : ((J.erase j).card : ℝ) = (J.card : ℝ) - 1 := by
      rw [hJcard, Nat.cast_sub hJ1]; norm_num
    have hc2 : ((n₂ + ((Q.filter (fun b => bidx b = j)).card - 1) : ℕ) : ℝ)
        = (n₂ : ℝ) + ((Q.filter (fun b => bidx b = j)).card : ℝ) - 1 := by
      have h1 : 1 ≤ (Q.filter (fun b => bidx b = j)).card := by omega
      rw [Nat.cast_add, Nat.cast_sub h1]; push_cast; ring
    have hq2 : (2 : ℝ) ≤ ((Q.filter (fun b => bidx b = j)).card : ℝ) := by exact_mod_cast hj2
    rw [hc1, hc2]
    rw [hsumJ, hsumQ] at hbud
    nlinarith [hcredj, mul_nonneg (by linarith :
      (0:ℝ) ≤ ((Q.filter (fun b => bidx b = j)).card : ℝ) - 2) hε]
  · rcases Classical.em (∃ j ∈ J, 2 ≤ (Lset.filter (fun g => g ∈ bg j)).card) with
      hcase2 | hcase2
    · -- **second transformation**: a bundle carrying two large available goods becomes a part
      obtain ⟨j, hjJ, hj2⟩ := hcase2
      obtain ⟨d₁, hd₁, d₂, hd₂, hne⟩ := Finset.one_lt_card.mp
        (by omega : 1 < (Lset.filter (fun g => g ∈ bg j)).card)
      have hd₁L : d₁ ∈ Lset := (Finset.mem_filter.mp hd₁).1
      have hd₂L : d₂ ∈ Lset := (Finset.mem_filter.mp hd₂).1
      have hd₁b : d₁ ∈ bg j := (Finset.mem_filter.mp hd₁).2
      have hd₂b : d₂ ∈ bg j := (Finset.mem_filter.mp hd₂).2
      have hd₁R : d₁ ∈ R := by
        have := (Finset.mem_filter.mp hd₁L).1; exact (Finset.mem_inter.mp this).1
      have hd₂R : d₂ ∈ R := by
        have := (Finset.mem_filter.mp hd₂L).1; exact (Finset.mem_inter.mp this).1
      have hd₁v : ε ≤ vbar w p d₁ := (Finset.mem_filter.mp hd₁L).2
      have hd₂v : ε ≤ vbar w p d₂ := (Finset.mem_filter.mp hd₂L).2
      have hcredj := cred_bundle_le w p hp bg wit bidx cred hwit_mem hcred_wit hbval hwout hinj j
      have hQcard : (Q.filter (fun b => bidx b = j)).card
          + (Q.filter (fun b => ¬ (bidx b = j))).card = Q.card :=
        Finset.card_filter_add_card_filter_not _
      have hsumQ : (∑ b ∈ Q, cred b)
          = (∑ b ∈ Q.filter (fun b => bidx b = j), cred b)
            + ∑ b ∈ Q.filter (fun b => ¬ (bidx b = j)), cred b :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hJcard : (J.erase j).card = J.card - 1 := Finset.card_erase_of_mem hjJ
      have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr ⟨j, hjJ⟩
      have hsumJ : (∑ j' ∈ J, vbarSum w p (bg j' ∩ R))
          = vbarSum w p (bg j ∩ R) + ∑ j' ∈ J.erase j, vbarSum w p (bg j' ∩ R) :=
        (Finset.add_sum_erase _ _ hjJ).symm
      -- the two goods leave the pool with the bundle they came from
      have hdS : ∀ d ∈ bg j, d ∉ Sset := by
        intro d hd hdS
        exact Finset.disjoint_left.mp (hbS j) hdS hd
      have hRsub : R \ ({d₁, d₂} : Finset G) ⊆ R := Finset.sdiff_subset
      have hSR' : Sset ⊆ R \ ({d₁, d₂} : Finset G) := by
        intro x hx
        refine Finset.mem_sdiff.mpr ⟨hSR hx, ?_⟩
        intro hxd
        rcases Finset.mem_insert.mp hxd with h | h
        · rw [h] at hx; exact hdS d₁ hd₁b hx
        · rw [Finset.mem_singleton.mp h] at hx; exact hdS d₂ hd₂b hx
      have hbginter : ∀ j' ∈ J.erase j, bg j' ∩ (R \ ({d₁, d₂} : Finset G)) = bg j' ∩ R := by
        intro j' hj'
        have hjj : j' ≠ j := (Finset.mem_erase.mp hj').1
        have hdisj := hbdisj j' j hjj
        ext x
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, h2, ?_⟩
          rintro (rfl | rfl)
          · exact Finset.disjoint_left.mp hdisj h1 hd₁b
          · exact Finset.disjoint_left.mp hdisj h1 hd₂b
      have hrec := ih (J.card - 1) (by omega) (R \ ({d₁, d₂} : Finset G)) (J.erase j)
        (Q.filter (fun b => ¬ (bidx b = j))) (k - 1)
        (n₂ + (Q.filter (fun b => bidx b = j)).card) hJcard hSR'
        (fun g hg => hsmall g (hRsub hg))
        (fun b hb => hwit_mem b (Finset.mem_filter.mp hb).1)
        (fun b hb => hcred_le b (Finset.mem_filter.mp hb).1)
        (fun b hb => hcred_wit b (Finset.mem_filter.mp hb).1)
        (fun b hb => fun hmem => hwout b (Finset.mem_filter.mp hb).1 (hRsub hmem))
        (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))
        (fun b hb => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hb).2,
          hbQ b (Finset.mem_filter.mp hb).1⟩)
        (by rw [hJcard]; omega) ?_
      · have hres := canonical_cons hD hRsub
          (by
            intro x hx
            rcases Finset.mem_insert.mp hx with h | h
            · rw [h]; exact hd₁R
            · rw [Finset.mem_singleton.mp h]; exact hd₂R)
          (Finset.disjoint_left.mpr (fun x hx hx' => (Finset.mem_sdiff.mp hx').2 hx))
          (pair_acceptable w p hne hd₁v hd₂v) hrec
        rwa [Nat.sub_add_cancel hk1] at hres
      · rw [Finset.sum_congr rfl (fun j' hj' => congrArg (vbarSum w p) (hbginter j' hj'))]
        have hc1 : ((J.erase j).card : ℝ) = (J.card : ℝ) - 1 := by
          rw [hJcard, Nat.cast_sub hJ1]; push_cast; ring
        have hqq : (0 : ℝ) ≤ ((Q.filter (fun b => bidx b = j)).card : ℝ) := Nat.cast_nonneg _
        rw [hc1]
        push_cast
        rw [hsumJ, hsumQ] at hbud
        nlinarith [hcredj, mul_nonneg hqq hε]
    · rcases Classical.em (2 ≤ Mix.card) with hcase3 | hcase3
      · -- **third transformation**: two mixed bundles give one pure part
        obtain ⟨j₁, hj₁M, j₂, hj₂M, hjne⟩ := Finset.one_lt_card.mp (by omega : 1 < Mix.card)
        have hj₁J : j₁ ∈ J := (Finset.mem_filter.mp hj₁M).1
        have hj₂J : j₂ ∈ J := (Finset.mem_filter.mp hj₂M).1
        obtain ⟨b₁, hb₁⟩ := (Finset.mem_filter.mp hj₁M).2.1
        obtain ⟨d₁, hd₁⟩ := (Finset.mem_filter.mp hj₁M).2.2
        obtain ⟨b₂, hb₂⟩ := (Finset.mem_filter.mp hj₂M).2.1
        obtain ⟨d₂, hd₂⟩ := (Finset.mem_filter.mp hj₂M).2.2
        have hd₁L : d₁ ∈ Lset := (Finset.mem_filter.mp hd₁).1
        have hd₂L : d₂ ∈ Lset := (Finset.mem_filter.mp hd₂).1
        have hd₁b : d₁ ∈ bg j₁ := (Finset.mem_filter.mp hd₁).2
        have hd₂b : d₂ ∈ bg j₂ := (Finset.mem_filter.mp hd₂).2
        have hne : d₁ ≠ d₂ := by
          intro h
          exact Finset.disjoint_left.mp (hbdisj j₁ j₂ hjne) hd₁b (h ▸ hd₂b)
        have hd₁R : d₁ ∈ R := (Finset.mem_inter.mp (Finset.mem_filter.mp hd₁L).1).1
        have hd₂R : d₂ ∈ R := (Finset.mem_inter.mp (Finset.mem_filter.mp hd₂L).1).1
        have hd₁v : ε ≤ vbar w p d₁ := (Finset.mem_filter.mp hd₁L).2
        have hd₂v : ε ≤ vbar w p d₂ := (Finset.mem_filter.mp hd₂L).2
        -- the two bundles and the events charged to them
        have hb₁Q : b₁ ∈ Q := (Finset.mem_filter.mp hb₁).1
        have hb₂Q : b₂ ∈ Q := (Finset.mem_filter.mp hb₂).1
        have hb₂j : bidx b₂ = j₂ := (Finset.mem_filter.mp hb₂).2
        have hq₁ : 1 ≤ (Q.filter (fun b => bidx b = j₁)).card :=
          Finset.card_pos.mpr ⟨b₁, hb₁⟩
        have hb₂mem : b₂ ∈ (Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hb₂Q, by rw [hb₂j]; exact hjne.symm⟩, hb₂j⟩
        have hq₂ : 1 ≤ ((Q.filter (fun b => ¬ (bidx b = j₁))).filter
            (fun b => bidx b = j₂)).card := Finset.card_pos.mpr ⟨b₂, hb₂mem⟩
        have hcred1 := cred_bundle_le w p hp bg wit bidx cred hwit_mem hcred_wit hbval hwout
          hinj j₁
        have hcred2 := cred_bundle_le w p hp bg wit bidx cred
          (R := R) (Q := Q.filter (fun b => ¬ (bidx b = j₁)))
          (fun b hb => hwit_mem b (Finset.mem_filter.mp hb).1)
          (fun b hb => hcred_wit b (Finset.mem_filter.mp hb).1) hbval
          (fun b hb => hwout b (Finset.mem_filter.mp hb).1)
          (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)) j₂
        have hQcard1 : (Q.filter (fun b => bidx b = j₁)).card
            + (Q.filter (fun b => ¬ (bidx b = j₁))).card = Q.card :=
          Finset.card_filter_add_card_filter_not _
        have hQcard2 : ((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂)).card
            + ((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => ¬ (bidx b = j₂))).card
              = (Q.filter (fun b => ¬ (bidx b = j₁))).card :=
          Finset.card_filter_add_card_filter_not _
        have hsumQ1 : (∑ b ∈ Q, cred b)
            = (∑ b ∈ Q.filter (fun b => bidx b = j₁), cred b)
              + ∑ b ∈ Q.filter (fun b => ¬ (bidx b = j₁)), cred b :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        have hsumQ2 : (∑ b ∈ Q.filter (fun b => ¬ (bidx b = j₁)), cred b)
            = (∑ b ∈ (Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂), cred b)
              + ∑ b ∈ (Q.filter (fun b => ¬ (bidx b = j₁))).filter
                  (fun b => ¬ (bidx b = j₂)), cred b :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        have hj₂erase : j₂ ∈ J.erase j₁ := Finset.mem_erase.mpr ⟨hjne.symm, hj₂J⟩
        have hJcard1 : (J.erase j₁).card = J.card - 1 := Finset.card_erase_of_mem hj₁J
        have hJcard2 : ((J.erase j₁).erase j₂).card = (J.erase j₁).card - 1 :=
          Finset.card_erase_of_mem hj₂erase
        have hJ2 : 2 ≤ J.card := by
          have : 1 ≤ (J.erase j₁).card := Finset.card_pos.mpr ⟨j₂, hj₂erase⟩
          omega
        have hsumJ1 : (∑ j' ∈ J, vbarSum w p (bg j' ∩ R))
            = vbarSum w p (bg j₁ ∩ R) + ∑ j' ∈ J.erase j₁, vbarSum w p (bg j' ∩ R) :=
          (Finset.add_sum_erase _ _ hj₁J).symm
        have hsumJ2 : (∑ j' ∈ J.erase j₁, vbarSum w p (bg j' ∩ R))
            = vbarSum w p (bg j₂ ∩ R)
              + ∑ j' ∈ (J.erase j₁).erase j₂, vbarSum w p (bg j' ∩ R) :=
          (Finset.add_sum_erase _ _ hj₂erase).symm
        have hRsub : R \ ({d₁, d₂} : Finset G) ⊆ R := Finset.sdiff_subset
        have hSR' : Sset ⊆ R \ ({d₁, d₂} : Finset G) := by
          intro x hx
          refine Finset.mem_sdiff.mpr ⟨hSR hx, ?_⟩
          intro hxd
          rcases Finset.mem_insert.mp hxd with h | h
          · rw [h] at hx; exact Finset.disjoint_left.mp (hbS j₁) hx hd₁b
          · rw [Finset.mem_singleton.mp h] at hx
            exact Finset.disjoint_left.mp (hbS j₂) hx hd₂b
        have hbginter : ∀ j' ∈ (J.erase j₁).erase j₂,
            bg j' ∩ (R \ ({d₁, d₂} : Finset G)) = bg j' ∩ R := by
          intro j' hj'
          have hjj₂ : j' ≠ j₂ := (Finset.mem_erase.mp hj').1
          have hjj₁ : j' ≠ j₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj').2).1
          ext x
          simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            refine ⟨h1, h2, ?_⟩
            rintro (rfl | rfl)
            · exact Finset.disjoint_left.mp (hbdisj j' j₁ hjj₁) h1 hd₁b
            · exact Finset.disjoint_left.mp (hbdisj j' j₂ hjj₂) h1 hd₂b
        have hrec := ih ((J.erase j₁).erase j₂).card (by omega)
          (R \ ({d₁, d₂} : Finset G)) ((J.erase j₁).erase j₂)
          ((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => ¬ (bidx b = j₂))) (k - 1)
          (n₂ + ((Q.filter (fun b => bidx b = j₁)).card
            + ((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂)).card - 1))
          rfl hSR' (fun g hg => hsmall g (hRsub hg))
          (fun b hb => hwit_mem b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1)
          (fun b hb => hcred_le b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1)
          (fun b hb => hcred_wit b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1)
          (fun b hb hmem => hwout b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
            (hRsub hmem))
          (hinj.mono (by
            intro x hx
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1))
          (fun b hb => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hb).2,
            Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2,
              hbQ b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1⟩⟩)
          (by omega) ?_
        · have hres := canonical_cons hD hRsub
            (by
              intro x hx
              rcases Finset.mem_insert.mp hx with h | h
              · rw [h]; exact hd₁R
              · rw [Finset.mem_singleton.mp h]; exact hd₂R)
            (Finset.disjoint_left.mpr (fun x hx hx' => (Finset.mem_sdiff.mp hx').2 hx))
            (pair_acceptable w p hne hd₁v hd₂v) hrec
          rwa [Nat.sub_add_cancel hk1] at hres
        · rw [Finset.sum_congr rfl (fun j' hj' => congrArg (vbarSum w p) (hbginter j' hj'))]
          have hc1 : (((J.erase j₁).erase j₂).card : ℝ) = (J.card : ℝ) - 2 := by
            have : ((J.erase j₁).erase j₂).card = J.card - 2 := by omega
            rw [this, Nat.cast_sub (by omega : 2 ≤ J.card)]; push_cast; ring
          have hc2 : ((n₂ + ((Q.filter (fun b => bidx b = j₁)).card
                + ((Q.filter (fun b => ¬ (bidx b = j₁))).filter
                    (fun b => bidx b = j₂)).card - 1) : ℕ) : ℝ)
              = (n₂ : ℝ) + (((Q.filter (fun b => bidx b = j₁)).card : ℝ)
                + (((Q.filter (fun b => ¬ (bidx b = j₁))).filter
                    (fun b => bidx b = j₂)).card : ℝ)) - 1 := by
            rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
          have hqq : (2 : ℝ) ≤ ((Q.filter (fun b => bidx b = j₁)).card : ℝ)
              + (((Q.filter (fun b => ¬ (bidx b = j₁))).filter (fun b => bidx b = j₂)).card : ℝ) := by
            have h1 : (1 : ℝ) ≤ ((Q.filter (fun b => bidx b = j₁)).card : ℝ) := by
              exact_mod_cast hq₁
            have h2 : (1 : ℝ) ≤ (((Q.filter (fun b => ¬ (bidx b = j₁))).filter
                (fun b => bidx b = j₂)).card : ℝ) := by exact_mod_cast hq₂
            linarith
          rw [hc1, hc2]
          rw [hsumJ1, hsumJ2, hsumQ1, hsumQ2] at hbud
          nlinarith [hcred1, hcred2, mul_nonneg (by linarith :
            (0:ℝ) ≤ ((Q.filter (fun b => bidx b = j₁)).card : ℝ)
              + (((Q.filter (fun b => ¬ (bidx b = j₁))).filter
                  (fun b => bidx b = j₂)).card : ℝ) - 2) hε]
      · -- **exit**: Proposition 6 applies
        push_neg at hcase1 hcase2
        haveI : NeZero k := ⟨by omega⟩
        have hLsub : Lset ⊆ R ∩ J.biUnion bg := by rw [hLset]; exact Finset.filter_subset _ _
        have hBunR : R ∩ J.biUnion bg ⊆ R := Finset.inter_subset_left
        have hSBun : Disjoint Sset (R ∩ J.biUnion bg) := by
          refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
          obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx').2
          exact Finset.disjoint_left.mp (hbS j) hx hj
        have hvS : ∀ g ∈ Sset, vbar w p g = p g := fun g hg => max_eq_left (hSwp g hg)
        -- the counting
        have hcount' : Lset.card + Q.card ≤ J.card + 1 := by
          refine exit_count bg hbdisj bidx hbQ ?_ ?_ ?_ (by rw [← hMix]; omega)
          · intro g hg
            have := Finset.mem_inter.mp (hLsub hg)
            obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp this.2
            exact ⟨j, hj, hgj⟩
          · intro j hj
            by_contra hcon
            exact absurd (by omega : 2 ≤ (Q.filter (fun b => bidx b = j)).card) (by
              have := hcase1 j hj; omega)
          · intro j hj
            by_contra hcon
            exact absurd (by omega : 2 ≤ (Lset.filter (fun g => g ∈ bg j)).card) (by
              have := hcase2 j hj; omega)
        have hLk : Lset.card ≤ k + (n₂ + 1) := by omega
        -- the resources handed to Proposition 6
        set Ssel : Finset G := Sset.filter (fun g => ε ≤ p g) with hSsel
        set Scheap : Finset G := Sset.filter (fun g => ¬ (ε ≤ p g)) with hScheap
        set Cset : Finset G := ((R ∩ J.biUnion bg) \ Lset) ∪ Scheap with hCset
        have hCdisj : Disjoint ((R ∩ J.biUnion bg) \ Lset) Scheap :=
          Finset.disjoint_left.mpr (fun x hx hx' =>
            Finset.disjoint_left.mp hSBun (Finset.mem_filter.mp hx').1
              (Finset.mem_sdiff.mp hx).1)
        have hAC : Disjoint Lset Cset := by
          refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
          rcases Finset.mem_union.mp hx' with h | h
          · exact (Finset.mem_sdiff.mp h).2 hx
          · exact Finset.disjoint_left.mp hSBun (Finset.mem_filter.mp h).1 (hLsub hx)
        have hAS : Disjoint Lset Ssel :=
          Finset.disjoint_left.mpr (fun x hx hx' =>
            Finset.disjoint_left.mp hSBun (Finset.mem_filter.mp hx').1 (hLsub hx))
        have hCS : Disjoint Cset Ssel := by
          refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
          rcases Finset.mem_union.mp hx with h | h
          · exact Finset.disjoint_left.mp hSBun (Finset.mem_filter.mp hx').1
              (Finset.mem_sdiff.mp h).1
          · exact (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp hx').2
        have hRsub'' : Lset ∪ Cset ∪ Ssel ⊆ R := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rcases Finset.mem_union.mp hx with hx | hx
            · exact hBunR (hLsub hx)
            · rcases Finset.mem_union.mp hx with hx | hx
              · exact hBunR (Finset.mem_sdiff.mp hx).1
              · exact hSR (Finset.mem_filter.mp hx).1
          · exact hSR (Finset.mem_filter.mp hx).1
        -- the value at our disposal
        have hBunsum : (∑ g ∈ R ∩ J.biUnion bg, vbar w p g)
            = ∑ j ∈ J, vbarSum w p (bg j ∩ R) := by
          have hBeq : R ∩ J.biUnion bg = J.biUnion (fun j => bg j ∩ R) := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_biUnion]
            constructor
            · rintro ⟨hxR, j, hj, hxj⟩; exact ⟨j, hj, hxj, hxR⟩
            · rintro ⟨j, hj, hxj, hxR⟩; exact ⟨hxR, j, hj, hxj⟩
          rw [hBeq, Finset.sum_biUnion]
          · rfl
          · intro x _ y _ hxy
            exact Finset.disjoint_of_subset_left Finset.inter_subset_left
              (Finset.disjoint_of_subset_right Finset.inter_subset_left (hbdisj x y hxy))
        have hsplitL : (∑ g ∈ (R ∩ J.biUnion bg) \ Lset, vbar w p g)
            + (∑ g ∈ Lset, vbar w p g) = ∑ g ∈ R ∩ J.biUnion bg, vbar w p g :=
          Finset.sum_sdiff hLsub
        have hCsum : (∑ g ∈ Cset, vbar w p g)
            = (∑ g ∈ (R ∩ J.biUnion bg) \ Lset, vbar w p g) + ∑ g ∈ Scheap, vbar w p g := by
          rw [hCset, Finset.sum_union hCdisj]
        have hScheapv : (∑ g ∈ Scheap, vbar w p g) = ∑ g ∈ Scheap, p g :=
          Finset.sum_congr rfl (fun g hg => hvS g (Finset.mem_filter.mp hg).1)
        have hSsum : (∑ g ∈ Ssel, p g) + (∑ g ∈ Scheap, p g) = ∑ g ∈ Sset, p g :=
          Finset.sum_filter_add_sum_filter_not _ _ _
        -- the budget available to Proposition 6
        have hcredsum : (∑ b ∈ Q, cred b) ≤ (Q.card : ℝ) * (3 * ε) := by
          calc (∑ b ∈ Q, cred b) ≤ ∑ _b ∈ Q, (3 * ε) := Finset.sum_le_sum (fun b hb => hcred_le b hb)
            _ = (Q.card : ℝ) * (3 * ε) := by rw [Finset.sum_const, nsmul_eq_mul]
        have hcast : (J.card : ℝ) = (k : ℝ) + (n₂ : ℝ) + (Q.card : ℝ) := by
          rw [← hcount]; push_cast; ring
        have hbudP : ((k : ℝ)) * (3 * ε) + (n₂ : ℝ) * ε
            ≤ (∑ g ∈ Lset, vbar w p g) + (∑ g ∈ Cset, vbar w p g) + D + ∑ g ∈ Ssel, p g := by
          rw [hCsum, hScheapv]
          rw [hcast] at hbud
          have h1 : (∑ g ∈ R ∩ J.biUnion bg, vbar w p g) = ∑ j ∈ J, vbarSum w p (bg j ∩ R) :=
            hBunsum
          nlinarith [hbud, hcredsum, hsplitL, hSsum, h1]
        have htle : (Lset.card - k : ℕ) ≤ n₂ + 1 := by omega
        have htler : ((Lset.card - k : ℕ) : ℝ) ≤ (n₂ : ℝ) + 1 := by exact_mod_cast htle
        have hmain := exists_canonical_of_large_pairs w p hp (μ := 3 * ε) (by linarith)
          (k := k) (R := Lset ∪ Cset ∪ Ssel) (D := D) hD (A := Lset) (C := Cset) (S := Ssel)
          rfl hAC hAS hCS
          (by
            intro g hg
            have := (Finset.mem_filter.mp (hLset ▸ hg : g ∈ (R ∩ J.biUnion bg).filter
              (fun g => ε ≤ vbar w p g))).2
            linarith)
          (by
            intro g hg
            have := hsmall g (hRsub'' hg)
            linarith)
          (by
            intro g hg
            rcases Finset.mem_union.mp hg with h | h
            · have hgB : g ∈ R ∩ J.biUnion bg := (Finset.mem_sdiff.mp h).1
              have hgL : g ∉ Lset := (Finset.mem_sdiff.mp h).2
              have : ¬ (ε ≤ vbar w p g) := by
                intro hcon
                exact hgL (by rw [hLset]; exact Finset.mem_filter.mpr ⟨hgB, hcon⟩)
              push_neg at this
              linarith
            · have h1 : ¬ (ε ≤ p g) := (Finset.mem_filter.mp h).2
              have h2 : vbar w p g = p g := hvS g (Finset.mem_filter.mp h).1
              push_neg at h1
              rw [h2]; linarith)
          (by
            intro g hg
            have := (Finset.mem_filter.mp hg).2
            linarith)
          (fun g hg => hSwp g (Finset.mem_filter.mp hg).1)
          (t := Lset.card - k) (by omega)
          (by
            have h3 : (3 : ℝ) * ε / 3 = ε := by ring
            rw [h3]
            have h4 : (2 : ℝ) * (3 * ε) / 3 = 2 * ε := by ring
            rw [h4]
            nlinarith [hbudP, htler, hε])
        have heq : (2 : ℝ) * (3 * ε) / 3 = 2 * ε := by ring
        rw [heq] at hmain
        exact (canonExists_of_nonempty hmain).mono hRsub'' le_rfl
end FairSelling
