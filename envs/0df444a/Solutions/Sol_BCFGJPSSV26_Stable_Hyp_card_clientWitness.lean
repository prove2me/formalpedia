-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Hyp.card_clientWitness
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:08:14.805193+00:00
-- url     : https://prove2.me/submissions/18fa57df-4210-4cbe-a53f-a5f43a24508c

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClientWitness
public import Definitions.Def_BCFGJPSSV26_Stable_Stability_FewNotInSync
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClientSampling
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClientSampling
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_O1_le
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt
public import Theorems.Thm_BCFGJPSSV26_Stable_guided_count

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace ClientSampling

section Analysis

variable (X : Ctx)

variable {X}

section Hyp

variable (H : Hyp X)
include H

theorem O1_sub_hit {Λ : List (Dummy X.I)} (hΛ : ∀ d ∈ Λ, GoodDum X d)
    (hs : X.s ≤ (hit X Λ).card) : X.O1 ⊆ hit X Λ := by
  have heq : hit X Λ = X.O1 := eq_of_subset_of_card_le (hit_sub_O1 hΛ) (H.card_O1_le.trans hs)
  intro c hc
  rw [heq]
  exact hc

theorem invL_add {t : ℕ} {Λ : List (Dummy X.I)} {j : Fin X.I.n} {c : Fin X.I.m} {r : ℝ}
    (h : InvL X t Λ) (hc : c ∈ X.O1) (hcn : c ∉ hit X Λ) (hj : j ∈ X.core (X.kap c) c)
    (hj6 : t < X.s → j ∈ X.core (6 * X.ε) c) (hr1 : X.dist j c ≤ r) (hr2 : r ≤ tgt X j c) :
    InvL X (t + 1) (Λ ++ [⟨.inl j, r⟩]) := by
  have hjC : j ∈ X.C c := core_sub_C _ _ hj
  have hcard : (hit X (Λ ++ [⟨.inl j, r⟩])).card = (hit X Λ).card + 1 := by
    rw [hit_append_mk hjC r, card_insert_of_notMem hcn]
  have hgood : ∀ d ∈ Λ ++ [⟨.inl j, r⟩], GoodDum X d := by
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.good.good d hd
    · rw [List.mem_singleton] at hd
      subst hd
      exact ⟨j, c, rfl, hc, hj, hr1, hr2⟩
  have hE : t + 1 ≤ X.s → ∀ d ∈ Λ ++ [⟨.inl j, r⟩], ∃ c, LedIn X d (X.core (6 * X.ε) c) := by
    intro ht d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact h.early (by omega) d hd
    · rw [List.mem_singleton] at hd
      subst hd
      exact ⟨c, ledIn_mk.2 (hj6 (by omega))⟩
  refine ⟨⟨hgood, ?_, ?_⟩, hE, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨h.good.pw, List.pairwise_singleton _ _, ?_⟩
    rintro a ha b hb ⟨c', hac, hbc⟩
    rw [List.mem_singleton] at hb
    subst hb
    have e : c' = c := eq_of_mem_C (ledIn_mk.1 hbc) hjC
    subst e
    exact hcn (mem_hit.2 ⟨mem_O_of_mem_C hjC, a, ha, hac⟩)
  · rw [hcard, h.good.card, List.length_append, List.length_singleton]
  · rcases h.c6 with h6 | ⟨ht, hcd⟩
    · exact Or.inl ((sum6_anti H.valid _ _).trans_lt h6)
    · by_cases hts : t + 1 < X.s
      · exact Or.inr ⟨hts, by omega⟩
      · left
        have hs : X.s ≤ (hit X (Λ ++ [⟨.inl j, r⟩])).card := by omega
        rw [sum6_eq_zero ((O1_sub_hit H hgood hs).trans (hit_sub_early (hE (by omega))))]
        exact thr_pos H
  · rcases h.cK with hK | ⟨ht, hcd⟩
    · exact Or.inl ((sumK_anti H.valid _ _).trans_lt hK)
    · by_cases hts : t + 1 < 2 * X.s
      · exact Or.inr ⟨hts, by omega⟩
      · left
        have hs : X.s ≤ (hit X (Λ ++ [⟨.inl j, r⟩])).card := by omega
        rw [sumK_eq_zero (O1_sub_hit H hgood hs)]
        exact thr_pos H

end Hyp

end Analysis

section Radius

variable {X : Ctx}

section Hyp

variable (H : Hyp X)
include H

end Hyp

end Radius

section Iteration

variable {X : Ctx} {LS : List ℕ}

variable (X LS)

variable {X LS}

section Hyp

variable (H : Hyp X)
include H

/-- **The step**: good chunks keep the invariant. -/
theorem inv_step {t : ℕ} {Λ : List DumQ} {u : Tri X} (hI : Inv X t Λ)
    (hG : GoodCh X LS t Λ u) : Inv X (t + 1) (stp X LS t Λ u) := by
  obtain ⟨hnp, hbit, hrad⟩ := hG
  rw [stp_eq]
  by_cases hb : cbit X.b u.2.1 = true
  · rw [if_pos hb]
    exact invL_skip hI fun hn ↦ hbit.1 hb (hnp hn)
  · rw [if_neg hb]
    have hacc : AccN X t Λ (smp X LS u.1) := by
      by_contra hn
      exact hb (hbit.2 hn)
    have hR := hrad hacc
    obtain ⟨h, c, hc, hj, hj6⟩ := hacc
    obtain ⟨hr1, hr2⟩ := hR h c (core_sub_C _ _ (pcore_sub_core _ _ hj))
    unfold Inv
    rw [toDums_append, toDums_single h]
    exact invL_add H hI (mem_sdiff.1 hc).1 (mem_sdiff.1 hc).2 (pcore_sub_core _ _ hj)
      (fun ht ↦ pcore_sub_core _ _ (hj6 ht)) hr1 hr2

end Hyp

end Iteration

section Density

variable {X : Ctx} {LS : List ℕ}

open Classical in
/-- **If progress is needed, a client of a missed cluster is sampled** with probability at
least `1/(8 N⁶)`: the acceptable clients carry at least `ε⁶ opt` of the weight `cost(S) ≤ 4 opt`.
-/
theorem card_acc_ge (H : Hyp X) (hLS : X.I.centers LS = X.S) (hLSm : ∀ i ∈ LS, i < X.I.m)
    {t : ℕ} {Λ : List DumQ} (hI : Inv X t Λ) (hn : NeedProg X t (toDums X.I Λ)) :
    (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) ≤
      (univ.filter fun us : Fin (2 ^ X.b) ↦ AccN X t Λ (smp X LS us)).card := by
  classical
  have hv := H.valid
  set Λ₁ := toDums X.I Λ with hΛ₁
  set Gs : Finset ℕ := (accSet X t Λ₁).image Fin.val with hGs
  -- the cores still to hit are expensive
  have hbig : X.ε ^ 5 * X.opt ≤ ∑ c ∈ X.O1 \ hit X Λ₁, X.costS (X.core (gam X t c) c) := by
    by_cases hts : t < X.s
    · have h6 : X.ε ^ 5 * X.opt ≤ sum6 X Λ₁ := by
        rcases hn with ⟨-, h⟩ | ⟨h', -⟩
        · exact h
        · omega
      have he : early X Λ₁ = hit X Λ₁ :=
        subset_antisymm (early_sub_hit _) (hit_sub_early (hI.early (by omega)))
      unfold sum6 at h6
      rw [he] at h6
      refine h6.trans (le_of_eq (sum_congr rfl fun c _ ↦ ?_))
      rw [gam, if_pos hts]
    · have hK : X.ε ^ 5 * X.opt ≤ sumK X Λ₁ := by
        rcases hn with ⟨h', -⟩ | ⟨-, h⟩
        · exact absurd h' hts
        · exact h
      refine hK.trans (le_of_eq (sum_congr rfl fun c _ ↦ ?_))
      rw [gam, if_neg hts]
  -- the sampled clients of `Gs` are acceptable
  have hsub : (univ.filter fun us : Fin (2 ^ X.b) ↦ wsample X.b (csW (toRaw X.I) LS) us ∈ Gs) ⊆
      (univ.filter fun us : Fin (2 ^ X.b) ↦ AccN X t Λ (smp X LS us)) := by
    intro us hus
    rw [mem_filter] at hus ⊢
    refine ⟨mem_univ _, ?_⟩
    obtain ⟨j, hj, hjl⟩ := mem_image.1 hus.2
    obtain ⟨c, hc, hjc⟩ := mem_biUnion.1 hj
    have e : smp X LS us = j.1 := hjl.symm
    unfold AccN
    rw [e]
    refine ⟨j.2, c, hc, ?_, fun hts ↦ ?_⟩
    · by_cases hts : t < X.s
      · rw [gam, if_pos hts] at hjc
        exact pcore_mono hv (six_eps_le_kappa H.eps_lt _) c hjc
      · rw [gam, if_neg hts] at hjc
        exact hjc
    · rw [gam, if_pos hts] at hjc
      exact hjc
  -- the weight of `Gs`
  have hpd : (↑(X.O1 \ hit X Λ₁) : Set (Fin X.I.m)).PairwiseDisjoint
      fun c ↦ pcore X (gam X t c) c := by
    intro c _ c' _ hne
    exact disjoint_of_subset_left ((pcore_sub_core _ _).trans (core_sub_C _ _))
      (disjoint_of_subset_right ((pcore_sub_core _ _).trans (core_sub_C _ _))
        (Instance.disjoint_cluster X.O hne))
  set M := ∑ i ∈ Gs, ((csW (toRaw X.I) LS).getD i 0 : ℝ) with hMdef
  have hmass : M = ∑ c ∈ X.O1 \ hit X Λ₁, X.costS (pcore X (gam X t c) c) := by
    rw [hMdef, hGs, sum_image Fin.val_injective.injOn, accSet, sum_biUnion hpd]
    refine sum_congr rfl fun c _ ↦ ?_
    unfold Ctx.costS Instance.costOn
    exact sum_congr rfl fun j _ ↦ csW_getD hLS hLSm j.2
  have hpunch : ∑ c ∈ X.O1 \ hit X Λ₁, X.costS (X.core (gam X t c) c) -
      X.ε ^ 6 * ∑ c ∈ X.O1 \ hit X Λ₁, ((X.C c).card * X.per c) ≤
        ∑ c ∈ X.O1 \ hit X Λ₁, X.costS (pcore X (gam X t c) c) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_le_sum fun c _ ↦ costS_pcore_ge hv _ c
  have hP := sum_card_per_le H (A := X.O1 \ hit X Λ₁) (sdiff_subset.trans sdiff_subset)
  have hPnn : 0 ≤ ∑ c ∈ X.O1 \ hit X Λ₁, ((X.C c).card * X.per c) :=
    sum_nonneg fun c _ ↦ mul_nonneg (Nat.cast_nonneg _) (per_nonneg hv _ _ _)
  have hopt : 0 < X.opt := H.opt_pos
  have hM : X.ε ^ 6 * X.opt ≤ M := by
    have := ar_mass H.eps_pos H.eps_lt hPnn hopt.le hP
    rw [hmass]
    linarith
  -- the weighted sample
  have hW := csW_sum hLS hLSm
  have hWle : X.I.costF X.S ≤ 4 * X.opt := costF_le_four_opt hv H.k_le_m X.P.hN H.alo
  have hWpos : 0 < X.I.costF X.S :=
    H.opt_pos.trans_le (Instance.opt_le_costF H.S_nonempty H.alo.1.le)
  have hWposQ : 0 < (csW (toRaw X.I) LS).sum := by
    have h := hW ▸ hWpos
    exact_mod_cast h
  have hGsl : ∀ i ∈ Gs, i < (csW (toRaw X.I) LS).length := by
    intro i hi
    rw [csW_length]
    obtain ⟨j, -, rfl⟩ := mem_image.1 hi
    exact j.2
  have hw := card_wsample (b := X.b) (csW_nonneg hv hLSm) hWposQ Gs hGsl
  rw [hW, ← hMdef] at hw
  have hGc : (Gs.card : ℝ) ≤ X.I.n := by
    have : Gs.card ≤ X.I.n := card_image_le.trans ((card_le_univ _).trans (by simp))
    exact_mod_cast this
  have hKn : (8 * X.I.n * (X.P.N : ℝ) ^ 6) ≤ 2 ^ X.b := by exact_mod_cast K_ge X
  have hN0 : (0 : ℝ) < X.P.N := X.P.N_pos'
  have hε6 : X.ε ^ 6 = 1 / (X.P.N : ℝ) ^ 6 := by
    rw [show X.ε = 1 / (X.P.N : ℝ) from rfl, one_div_pow]
  have hK0 : (0 : ℝ) < 2 ^ X.b := by positivity
  have h1 : (2 ^ X.b : ℝ) * X.ε ^ 6 / 4 ≤ (2 ^ X.b : ℝ) * M / X.I.costF X.S := by
    rw [div_le_div_iff₀ (by norm_num) hWpos]
    have hε0 : 0 < X.ε ^ 6 := pow_pos H.eps_pos 6
    have a1 := mul_le_mul_of_nonneg_left hWle (mul_pos hK0 hε0).le
    have a2 := mul_le_mul_of_nonneg_left hM hK0.le
    nlinarith
  have hnle : (X.I.n : ℝ) ≤ (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) =
        (2 ^ X.b : ℝ) * X.ε ^ 6 / 4 - (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) := by
          rw [hε6]
          field_simp
          ring
    _ ≤ (2 ^ X.b : ℝ) * X.ε ^ 6 / 4 - X.I.n := by linarith
    _ ≤ (2 ^ X.b : ℝ) * M / X.I.costF X.S - Gs.card := by linarith
    _ ≤ _ := hw
    _ ≤ _ := by exact_mod_cast card_le_card hsub

open Classical in
/-- **The density** of the good chunks is at least `q₁ = 1/(440 N⁸)`. -/
theorem density (H : Hyp X) (hLS : X.I.centers LS = X.S) (hLSm : ∀ i ∈ LS, i < X.I.m)
    {t : ℕ} {Λ : List DumQ} (hI : Inv X t Λ) :
    X.P.q₁ * (Fintype.card (Tri X) : ℝ) ≤ (univ.filter fun u ↦ GoodCh X LS t Λ u).card := by
  have hb1 : 1 ≤ X.b := by
    have := X.P.hN
    unfold Ctx.b Par.bits
    omega
  have hN : (201 : ℝ) ≤ X.P.N := X.P.N_ge
  have hGr : (Par.Gr X.P.N : ℝ) = 10 * (X.P.N : ℝ) ^ 2 + 1 := by
    unfold Par.Gr
    push_cast
    ring
  have hGr1 : (1 : ℝ) ≤ Par.Gr X.P.N := by exact_mod_cast Gr_pos X.P.N
  have hK0 : (0 : ℝ) < 2 ^ X.b := by positivity
  set A : Finset (Fin (2 ^ X.b)) := if NeedProg X t (toDums X.I Λ) then
    univ.filter (fun us ↦ AccN X t Λ (smp X LS us)) else univ with hAdef
  have hAmem : ∀ us ∈ A, NeedProg X t (toDums X.I Λ) → AccN X t Λ (smp X LS us) := by
    intro us hus hn
    rw [hAdef, if_pos hn] at hus
    exact (mem_filter.1 hus).2
  have hA : (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) ≤ A.card := by
    by_cases hn : NeedProg X t (toDums X.I Λ)
    · rw [hAdef, if_pos hn]
      exact card_acc_ge H hLS hLSm hI hn
    · rw [hAdef, if_neg hn, card_univ, Fintype.card_fin]
      push_cast
      refine div_le_self hK0.le ?_
      have : (1 : ℝ) ≤ (X.P.N : ℝ) ^ 6 := one_le_pow₀ (by linarith)
      linarith
  have hfib : ∀ us ∈ A, (2 : ℝ) ^ (X.b - 1) * ((2 ^ X.b : ℝ) / (2 * Par.Gr X.P.N)) ≤
      (univ.filter fun p : Fin (2 ^ X.b) × Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, p)).card := by
    intro us hus
    by_cases hacc : AccN X t Λ (smp X LS us)
    · obtain ⟨x₀, hx₀, hrad⟩ := rad_choice H hLS hLSm hacc
      have h1 := card_prod_ge (fun p : Fin (2 ^ X.b) × Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, p))
        (univ.filter fun uk : Fin (2 ^ X.b) ↦ cbit X.b uk = false)
        ((2 ^ X.b : ℝ) / (2 * Par.Gr X.P.N)) (fun uk huk ↦ ?_)
      · rw [card_cbit hb1] at h1
        push_cast at h1
        exact h1
      · refine (card_cunif (Gr_pos X.P.N) (Gr_le_K H) hx₀).trans ?_
        have hsub : (univ.filter fun ur : Fin (2 ^ X.b) ↦ cunif (Par.Gr X.P.N) ur = x₀) ⊆
            (univ.filter fun ur : Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, (uk, ur))) := by
          intro ur hur
          refine mem_filter.2 ⟨mem_univ _, fun _ ↦ hacc, ⟨fun hcb ↦ ?_, fun hn ↦ absurd hacc hn⟩,
            fun _ ↦ hrad ur (mem_filter.1 hur).2⟩
          have hf := (mem_filter.1 huk).2
          rw [hf] at hcb
          exact absurd hcb Bool.false_ne_true
        exact_mod_cast card_le_card hsub
    · have h1 := card_prod_ge (fun p : Fin (2 ^ X.b) × Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, p))
        (univ.filter fun uk : Fin (2 ^ X.b) ↦ cbit X.b uk = true)
        ((2 ^ X.b : ℝ) / (2 * Par.Gr X.P.N)) (fun uk huk ↦ ?_)
      · rw [card_cbit hb1] at h1
        push_cast at h1
        exact h1
      · have hall : (univ.filter fun ur : Fin (2 ^ X.b) ↦ GoodCh X LS t Λ (us, (uk, ur))) =
            univ := by
          refine eq_univ_of_forall fun ur ↦ mem_filter.2 ⟨mem_univ _,
            fun hn ↦ absurd (hAmem us hus hn) hacc, ⟨fun _ ↦ hacc, fun _ ↦ (mem_filter.1 huk).2⟩,
            fun h ↦ absurd h hacc⟩
        rw [hall, card_univ, Fintype.card_fin]
        push_cast
        refine div_le_self hK0.le ?_
        linarith
  have h := card_prod_ge (fun u : Tri X ↦ GoodCh X LS t Λ u) A _ hfib
  refine le_trans ?_ h
  have hcardT : (Fintype.card (Tri X) : ℝ) = (2 ^ X.b : ℝ) ^ 3 := by
    simp only [Tri, Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have h2b : (2 : ℝ) ^ (X.b - 1) = (2 ^ X.b : ℝ) / 2 := by
    rw [eq_div_iff two_ne_zero, ← pow_succ, Nat.sub_add_cancel hb1]
  rw [hcardT, h2b]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hA (by positivity))
  have hN1 : (1 : ℝ) ≤ X.P.N := by linarith
  have hN0 : (0 : ℝ) < X.P.N := by linarith
  have e : (2 ^ X.b : ℝ) / (8 * X.P.N ^ 6) *
      ((2 ^ X.b : ℝ) / 2 * ((2 ^ X.b : ℝ) / (2 * Par.Gr X.P.N))) =
        (2 ^ X.b : ℝ) ^ 3 / (32 * X.P.N ^ 6 * (10 * X.P.N ^ 2 + 1)) := by
    rw [hGr]
    field_simp
    ring
  rw [e, Prm.q₁, div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (ar_q hN1)

end Density

section Triples

end Triples

end ClientSampling

open ClientSampling in
open Classical in
/-- **The process lemma of the client sampling.** -/
theorem Hyp.card_clientWitness {X : Ctx} (H : Hyp X) {LS : List ℕ} (hLS : X.I.centers LS = X.S)
    (hLSnd : LS.Nodup) (hLSm : ∀ i ∈ LS, i < X.I.m) :
    X.P.q₁ ^ (2 * X.s) * ((2 : ℝ) ^ X.b) ^ (6 * X.s) ≤
      (univ.filter fun u : Fin (6 * X.s) → Fin (2 ^ X.b) ↦
        Nonempty (ClientWitness X
          (toDums X.I (csRun X.P.N (toRaw X.I) LS X.s X.b (toCh u))))).card := by
  have _ := hLSnd
  have hq : 0 ≤ X.P.q₁ := by
    unfold Prm.q₁
    positivity
  have hg := guided_count (stp X LS) ([] : List DumQ) (Inv X) (GoodCh X LS) hq (2 * X.s)
    (invL_zero H) (fun t _ Λ u hI hG ↦ inv_step H hI hG) (fun t _ Λ hI ↦ density H hLS hLSm hI)
  have hcard : (Fintype.card (Tri X) : ℝ) ^ (2 * X.s) = ((2 : ℝ) ^ X.b) ^ (6 * X.s) := by
    simp only [Tri, Fintype.card_prod, Fintype.card_fin]
    push_cast
    rw [show 6 * X.s = 3 * (2 * X.s) by ring, pow_mul]
    ring
  rw [hcard] at hg
  refine hg.trans ?_
  have hmaps : ∀ v ∈ (univ.filter fun v : Fin (2 * X.s) → Tri X ↦
      Inv X (2 * X.s) (runFin (stp X LS) [] (2 * X.s) v)),
      spread v ∈ (univ.filter fun u : Fin (6 * X.s) → Fin (2 ^ X.b) ↦
        Nonempty (ClientWitness X
          (toDums X.I (csRun X.P.N (toRaw X.I) LS X.s X.b (toCh u))))) := by
    intro v hv
    rw [mem_filter] at hv ⊢
    refine ⟨mem_univ _, ?_⟩
    have e : csRun X.P.N (toRaw X.I) LS X.s X.b (toCh (spread v)) =
        runFin (stp X LS) [] (2 * X.s) v :=
      foldl_eq_runFin X LS _ v _ fun i hi ↦ toCh_spread v i hi
    rw [e]
    have hI := hv.2
    exact witness H hI.good (hI.c6.resolve_right (by omega)) (hI.cK.resolve_right (by omega))
  exact_mod_cast card_le_card_of_injOn spread (fun v hv ↦ hmaps v hv)
    (fun v _ v' _ h ↦ spread_injective h)

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Hyp.card_clientWitness := @BCFGJPSSV26.Stable.Hyp.card_clientWitness
