-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.rowRadiusAssembly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:38.367802+00:00
-- url     : https://prove2.me/submissions/cfd1c5d6-8d32-4e01-8fc5-5b5a2085b7e2

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_sum_odd_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_top
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_capacity_le_reachCapacity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_cost_nonneg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_row

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ThmAAssembly := by
  intro l d _ hl hd hde TT nu1 nu2 size hn21 hn1s sig hsig ι _ lt isTop spec κ htop htopsum hnonsum
    hspec hcap
  classical
  have hl2 : 2 ≤ l := by omega
  have hsig0 : ∀ s, 0 ≤ sig s := fun s => (hsig.1.1 s).1
  obtain ⟨R, hRdef⟩ : ∃ R : Finset ℕ, R = ((Finset.univ.image
      (fun i => (spec i).elim (0 : ℤ) Prod.snd)).filter (fun j => 0 < j)).image Int.toNat :=
    ⟨_, rfl⟩
  have hRodd : ∀ j ∈ R, Odd j := by
    intro j hj
    rw [hRdef] at hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨k, ⟨⟨i, rfl⟩, hk⟩, rfl⟩ := hj
    rcases hsp : spec i with _ | ⟨s, j'⟩
    · rw [hsp] at hk
      simp at hk
    · obtain ⟨_, hodd, _⟩ := hspec i s j' hsp
      rw [hsp] at hk
      simp only [Option.elim] at hk ⊢
      have h1 : ((j'.toNat : ℕ) : ℤ) = j' := Int.toNat_of_nonneg hk.le
      exact (Int.odd_coe_nat _).mp (by rw [h1]; exact hodd)
  have hex : ∀ s, ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, dTop d TT s = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      topTerm l d TT nu1 nu2 s + ((nu1 s : ℝ) * ε +
        ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * ε) 0) ≤
        (nu1 s : ℝ) * gam l :=
    fun s => asmA_top l d hl2 TT nu1 nu2 s R hRodd
  choose eps heps0 hepsD hepsT using hex
  refine ⟨eps, heps0, fun s _ e he => hepsD s e he, ?_⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ι → ℝ, ∀ i, X i = if isTop i = true then (κ i : ℝ) * (gam l - eps (lt i))
      else (κ i : ℝ) * (gam l - sig (lt i)) := ⟨_, fun _ => rfl⟩
  have hrow : ∀ i, X i - (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i) := fun i => by
    rw [hXdef]
    exact asmA_row l sig eps hsig0 lt isTop spec κ i (fun h => (htop i h).2)
  have hX : ∑ i, X i = ∑ s ∈ TT, (nu1 s : ℝ) * (gam l - eps s) +
      Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) := by
    rw [hsig.2, ← Finset.sum_fiberwise Finset.univ lt X]
    have hs : ∀ s : ZMod d, ∑ i ∈ Finset.univ.filter (fun i => lt i = s), X i =
        (if s ∈ TT then (nu1 s : ℝ) * (gam l - eps s) else 0) +
          (Dl d TT nu1 size s : ℝ) * (gam l - sig s) := by
      intro s
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun i => isTop i = true),
        Finset.filter_filter, Finset.filter_filter]
      rw [Finset.filter_congr (p := fun i => lt i = s ∧ ¬isTop i = true)
        (q := fun i => lt i = s ∧ isTop i = false) (fun i _ => by simp)]
      congr 1
      · have e1 : ∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), X i =
            (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), (κ i : ℝ)) *
              (gam l - eps s) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_filter] at hi
          rw [hXdef, if_pos hi.2.2, hi.2.1]
        rw [e1]
        split_ifs with hsT
        · rw [htopsum s hsT]
        · have hem : Finset.univ.filter (fun i => lt i = s ∧ isTop i = true) = ∅ := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, not_and]
            intro h1 h2
            exact hsT (h1 ▸ (htop i h2).1)
          rw [hem]
          simp
      · have e2 : ∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), X i =
            (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), (κ i : ℝ)) *
              (gam l - sig s) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_filter] at hi
          rw [hXdef, if_neg (by rw [hi.2.2]; exact Bool.false_ne_true), hi.2.1]
        rw [e2, hnonsum s]
    rw [Finset.sum_congr rfl (fun s _ => hs s), Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter]
  obtain ⟨P, hPdef⟩ : ∃ P : Finset (ZMod d × ℤ), P = Finset.univ.biUnion (fun i => (spec i).toFinset) :=
    ⟨_, rfl⟩
  have hPmem : ∀ p ∈ P, ∃ i, spec i = some p := by
    intro p hp
    rw [hPdef, Finset.mem_biUnion] at hp
    obtain ⟨i, _, hi⟩ := hp
    exact ⟨i, Option.mem_toFinset.mp hi⟩
  have hstepA : ∑ i, (κ i : ℝ) * asmA_cost l eps (spec i) =
      ∑ p ∈ P, (∑ i ∈ Finset.univ.filter (fun i => spec i = some p), (κ i : ℝ)) *
        asmA_cost l eps (some p) := by
    have hR : ∑ p ∈ P, (∑ i ∈ Finset.univ.filter (fun i => spec i = some p), (κ i : ℝ)) *
        asmA_cost l eps (some p) = ∑ i, ∑ p ∈ P,
          (if spec i = some p then (κ i : ℝ) * asmA_cost l eps (some p) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_mul, Finset.sum_filter]
    rw [hR]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hsp : spec i with _ | p0
    · simp [asmA_cost]
    · have hp0 : p0 ∈ P := by
        rw [hPdef, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ _, Option.mem_toFinset.mpr hsp⟩
      rw [Finset.sum_eq_single p0]
      · simp
      · intro p _ hp
        rw [if_neg]
        intro h
        exact hp (Option.some_injective _ h).symm
      · intro h
        exact absurd hp0 h
  have hstepB : ∑ p ∈ P, (∑ i ∈ Finset.univ.filter (fun i => spec i = some p), (κ i : ℝ)) *
        asmA_cost l eps (some p) ≤
      ∑ p ∈ P, (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p) :=
    Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_right (hcap p.1 p.2) (asmA_cost_nonneg l eps _)
  have hpos : ∑ p ∈ P.filter (fun p => 0 < p.2),
        (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p) ≤
      ∑ s ∈ TT, ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * eps s) 0 := by
    obtain ⟨G, hG⟩ : ∃ G : ZMod d × ℕ → ℝ, ∀ x, G x =
        (capL d TT nu1 nu2 (x.1 + (x.2 : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ x.2 * eps x.1) 0 :=
      ⟨_, fun _ => rfl⟩
    have hinj : Set.InjOn (fun p : ZMod d × ℤ => (p.1, p.2.toNat))
        (P.filter (fun p => 0 < p.2) : Set (ZMod d × ℤ)) := by
      rintro ⟨a, j⟩ hp ⟨b, j'⟩ hp' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp')).2
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by omega⟩
    calc ∑ p ∈ P.filter (fun p => 0 < p.2),
          (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p)
        = ∑ p ∈ P.filter (fun p => 0 < p.2), G (p.1, p.2.toNat) := by
          refine Finset.sum_congr rfl ?_
          rintro ⟨s, j⟩ hp
          have hj := (Finset.mem_filter.mp hp).2
          have hcast : ((j.toNat : ℕ) : ZMod d) = (j : ZMod d) := by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg hj.le]
          rw [hG]
          dsimp only at hj ⊢
          simp only [asmA_cost, if_pos hj, hcast]
      _ = ∑ x ∈ (P.filter (fun p => 0 < p.2)).image (fun p : ZMod d × ℤ => (p.1, p.2.toNat)), G x :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ x ∈ TT ×ˢ R, G x := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨⟨s, j⟩, hp, rfl⟩ := hx
            rw [Finset.mem_filter] at hp
            obtain ⟨i, hi⟩ := hPmem _ hp.1
            obtain ⟨hsT, -⟩ := hspec i s j hi
            rw [Finset.mem_product]
            refine ⟨hsT, ?_⟩
            rw [hRdef]
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, ⟨⟨i, by rw [hi]; rfl⟩, hp.2⟩, rfl⟩
          · intro x _ _
            rw [hG]
            exact mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
      _ = _ := by
          rw [Finset.sum_product]
          simp only [hG]
  have hneg : ∑ p ∈ P.filter (fun p => ¬ 0 < p.2),
        (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p) ≤
      ∑ s ∈ TT, gam l * (Wcap l d TT nu1 nu2 size s : ℝ) := by
    have hmaps : ∀ p ∈ P.filter (fun p => ¬ 0 < p.2), p.1 ∈ TT := by
      intro p hp
      obtain ⟨i, hi⟩ := hPmem p (Finset.mem_filter.mp hp).1
      exact (hspec i p.1 p.2 hi).1
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum fun s _ => ?_
    obtain ⟨Q, hQ⟩ : ∃ Q : Finset (ZMod d × ℤ),
        Q = (P.filter (fun p => ¬ 0 < p.2)).filter (fun p => p.1 = s) := ⟨_, rfl⟩
    rw [← hQ]
    have hQmem : ∀ p ∈ Q, p.1 = s ∧ p.2 < 0 ∧ Odd p.2 ∧ ∃ i, spec i = some p := by
      intro p hp
      rw [hQ, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨hpP, hn⟩, hps⟩ := hp
      obtain ⟨i, hi⟩ := hPmem p hpP
      have ho := (hspec i p.1 p.2 hi).2.1
      have hne : p.2 ≠ 0 := by
        obtain ⟨k, hk⟩ := ho
        omega
      exact ⟨hps, by omega, ho, i, hi⟩
    have hinj2 : Set.InjOn (fun p : ZMod d × ℤ => (-p.2).toNat) (Q : Set (ZMod d × ℤ)) := by
      rintro ⟨a, j⟩ hp ⟨b, j'⟩ hp' h
      have h1 := hQmem _ (Finset.mem_coe.mp hp)
      have h2 := hQmem _ (Finset.mem_coe.mp hp')
      dsimp only at h h1 h2
      rw [Prod.mk.injEq]
      exact ⟨h1.1.trans h2.1.symm, by omega⟩
    have hoddN : ∀ n ∈ Q.image (fun p : ZMod d × ℤ => (-p.2).toNat), Odd n := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨⟨a, j⟩, hp, rfl⟩ := hn
      obtain ⟨-, hj, hodd, -⟩ := hQmem _ hp
      dsimp only at hj hodd ⊢
      have h1 : (((-j).toNat : ℕ) : ℤ) = -j := Int.toNat_of_nonneg (by omega)
      exact (Int.odd_coe_nat _).mp (by rw [h1]; exact hodd.neg)
    calc ∑ p ∈ Q, (capL d TT nu1 nu2 (p.1 + (p.2 : ZMod d)) : ℝ) * asmA_cost l eps (some p)
        ≤ ∑ p ∈ Q, (Wcap l d TT nu1 nu2 size s : ℝ) * ((l : ℝ) ^ (-p.2).toNat)⁻¹ := by
          refine Finset.sum_le_sum ?_
          rintro ⟨s', j⟩ hp
          obtain ⟨hs', hj, hodd, i, hi⟩ := hQmem _ hp
          dsimp only at hs' hj hodd hi ⊢
          subst hs'
          obtain ⟨-, -, hlt, -, hsz⟩ := hspec i s' j hi
          have hsz' := hsz hj
          rw [hlt] at hsz'
          simp only [asmA_cost, if_neg (not_lt.mpr hj.le)]
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast capacity_le_reachCapacity l d TT nu1 nu2 size s' j hj hodd hsz') (by positivity)
      _ = (Wcap l d TT nu1 nu2 size s : ℝ) *
            ∑ n ∈ Q.image (fun p : ZMod d × ℤ => (-p.2).toNat), ((l : ℝ) ^ n)⁻¹ := by
          rw [Finset.mul_sum, Finset.sum_image hinj2]
      _ ≤ (Wcap l d TT nu1 nu2 size s : ℝ) * gam l :=
          mul_le_mul_of_nonneg_left (asmA_sum_odd_le l hl2 _ hoddN) (Nat.cast_nonneg _)
      _ = gam l * (Wcap l d TT nu1 nu2 size s : ℝ) := mul_comm _ _
  have hcost : ∑ i, (κ i : ℝ) * asmA_cost l eps (spec i) ≤
      ∑ s ∈ TT, ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * eps s) 0 +
        ∑ s ∈ TT, gam l * (Wcap l d TT nu1 nu2 size s : ℝ) := by
    rw [hstepA]
    refine le_trans hstepB ?_
    rw [← Finset.sum_filter_add_sum_filter_not P (fun p => 0 < p.2)]
    exact add_le_add hpos hneg
  have hsr := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hrow i)
  rw [Finset.sum_sub_distrib] at hsr
  have hT : ∑ s ∈ TT, topTerm l d TT nu1 nu2 s ≤ ∑ s ∈ TT, (nu1 s : ℝ) * (gam l - eps s) -
      ∑ s ∈ TT, ∑ j ∈ R, (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ) * max (1 - (l : ℝ) ^ j * eps s) 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [mul_sub]
    linarith [hepsT s]
  rw [Finset.sum_sub_distrib]
  linarith [hX, hcost, hT, hsr]
end Formalism.DworkPowerSeriesWeights
