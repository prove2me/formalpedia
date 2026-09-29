-- Prove2me | solution 1 for Deformation.PLoc.isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/157c2e37-c32f-5642-8bb1-19afd18a71bf

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

universe u

namespace Deformation
p2m_export "Deformation" "PLoc.IsPadicLimit PLoc.wPartialSum PLoc.wSeries"
namespace PLoc
p2m_export "Deformation.PLoc" "invPow invPow_mul_algebraMap_pow_add pSub algebraMap_mem_powSub_of_mem IsPadicLimit wPartialSum wPartialSum_succ wSeries isPadicLimit_wSeries"
namespace EConv
p2m_open "Deformation.PLoc Deformation"

p2m_open "Deformation P2MW.S_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span.Deformation Deformation.PLoc P2MW.S_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span.Deformation.PLoc"

section Conv

variable (p : ℕ) [hp : Fact p.Prime]

theorem add_self_le_prime_pow (k : ℕ) : k + k ≤ p ^ k := by
  have h2 : 2 ≤ p := hp.out.two_le
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using h2
    · have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
      have hk' : 2 ≤ p ^ k := by
        calc 2 ≤ k + k := by omega
          _ ≤ p ^ k := ih
      calc k + 1 + (k + 1) = (k + k) + 2 := by ring
        _ ≤ p ^ k + p ^ k := Nat.add_le_add ih hk'
        _ = 2 * p ^ k := by ring
        _ ≤ p * p ^ k := Nat.mul_le_mul_right _ h2
        _ = p ^ (k + 1) := by ring

theorem le_prime_pow_sub_self (k : ℕ) : k ≤ p ^ k - k := by
  have := add_self_le_prime_pow p k
  omega

theorem self_le_prime_pow (k : ℕ) : k ≤ p ^ k := by
  have := add_self_le_prime_pow p k
  omega

variable {g : Type*} [CommRing g]

theorem isPadicLimit_wPartialSum_wSeries_of_forall_mem [IsAdicComplete (Ideal.span {(p : g)}) g]
    (c : ℕ → g) (n : ℕ) (hc : ∀ k, n ≤ k → c k ∈ Ideal.span {(p : g)}) :
    IsPadicLimit p (wPartialSum p c) (wSeries p c) := by
  apply isPadicLimit_wSeries

  have hb : ∀ k, ∃ b : g, n ≤ k → c k = (p : g) * b := fun k => by
    by_cases hk : n ≤ k
    · obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hc k hk)
      exact ⟨b, fun _ => by rw [← hb, mul_comm]⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose b hb using hb
  set u : ℕ → g := fun k => (p : g) ^ (p ^ k - k) * b k ^ p ^ k with hu_def
  have hu : ∀ k, n ≤ k →
      invPow p g k * algebraMap g (Localization.Away (p : g)) (c k ^ p ^ k) =
        algebraMap g (Localization.Away (p : g)) (u k) := by
    intro k hk
    have hsplit : (p : g) ^ p ^ k = (p : g) ^ (k + (p ^ k - k)) := by
      rw [Nat.add_sub_cancel' (self_le_prime_pow p k)]
    rw [hb k hk, mul_pow, map_mul, ← mul_assoc, hsplit, invPow_mul_algebraMap_pow_add, ← map_mul]

  let T : ℕ → g := fun N => ∑ k ∈ Finset.Ico n N, u k
  have hT_def : ∀ N, T N = ∑ k ∈ Finset.Ico n N, u k := fun N => rfl
  have hT : ∀ N, n ≤ N → wPartialSum p c N =
      wPartialSum p c n + algebraMap g (Localization.Away (p : g)) (T N) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rw [hT_def, Finset.Ico_self, Finset.sum_empty, map_zero, add_zero]
    | succ N hN ih =>
      rw [wPartialSum_succ, ih, hT_def, hT_def, Finset.sum_Ico_succ_top hN, map_add, hu N hN, add_assoc]
  have hu_mem : ∀ m k, m ≤ k → u k ∈ Ideal.span {(p : g)} ^ m := by
    intro m k hmk
    rw [Ideal.span_singleton_pow]
    have hle : m ≤ p ^ k - k := hmk.trans (le_prime_pow_sub_self p k)
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
    refine Ideal.mem_span_singleton'.2 ⟨(p : g) ^ t * b k ^ p ^ k, ?_⟩
    rw [hu_def]
    simp only
    rw [ht, pow_add]
    ring
  have hcauchy : ∀ m N N', m ≤ N → N ≤ N' → n ≤ N → T N' - T N ∈ Ideal.span {(p : g)} ^ m := by
    intro m N N' hmN hNN' hnN
    have : T N' - T N = ∑ k ∈ Finset.Ico N N', u k := by
      rw [hT_def, hT_def, ← Finset.sum_Ico_consecutive _ hnN hNN', add_sub_cancel_left]
    rw [this]
    exact Ideal.sum_mem _ fun k hk => hu_mem m k (hmN.trans (Finset.mem_Ico.1 hk).1)

  let f : ℕ → g := fun m => T (max n m)
  have hf_def : ∀ m, f m = T (max n m) := fun m => rfl
  have hf : ∀ {m m' : ℕ}, m ≤ m' → f m ≡ f m' [SMOD (Ideal.span {(p : g)} ^ m • ⊤ : Submodule g g)] := by
    intro m m' hmm'
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (hcauchy m _ _ (le_max_right _ _) (max_le_max le_rfl hmm') (le_max_left _ _))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : g)}) g) @hf
  refine ⟨wPartialSum p c n + algebraMap g (Localization.Away (p : g)) L, fun s => ⟨max n s, fun N hN => ?_⟩⟩
  have hnN : n ≤ N := (le_max_left _ _).trans hN
  have hsN : s ≤ N := (le_max_right _ _).trans hN
  rw [hT N hnN, add_sub_add_left_eq_sub, ← map_sub]
  apply algebraMap_mem_powSub_of_mem
  have h1 : T N - L ∈ Ideal.span {(p : g)} ^ N := by
    have := hL N
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    rwa [hf_def, max_eq_right hnN] at this
  rw [← Ideal.span_singleton_pow]
  exact Ideal.pow_le_pow_right hsN h1

theorem exists_forall_wSeries_sub_wPartialSum_mem_pSub_of_forall_mem [IsAdicComplete (Ideal.span {(p : g)}) g]
    (c : ℕ → g) (n : ℕ) (hc : ∀ k, n ≤ k → c k ∈ Ideal.span {(p : g)}) :
    ∃ N : ℕ, ∀ n', N ≤ n' → wSeries p c - wPartialSum p c n' ∈ pSub p g := by
  obtain ⟨N, hN⟩ := isPadicLimit_wPartialSum_wSeries_of_forall_mem p c n hc 1
  refine ⟨N, fun n' hn' => ?_⟩
  rw [← neg_sub]
  exact neg_mem (hN n' hn')

end Conv

end Deformation.PLoc.EConv

theorem solution
    (p : ℕ) [Fact p.Prime] (g : Type u) [CommRing g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    (c : ℕ → g) (hc : ∃ n : ℕ, ∀ k, n ≤ k → c k ∈ Ideal.span {(p : g)}) :
    Deformation.PLoc.IsPadicLimit p (Deformation.PLoc.wPartialSum p c) (Deformation.PLoc.wSeries p c) := by
  obtain ⟨n, hn⟩ := hc
  exact Deformation.PLoc.EConv.isPadicLimit_wPartialSum_wSeries_of_forall_mem p c n hn

end S_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span
end P2MW
export P2MW.S_Deformation_PLoc_isPadicLimit_wPartialSum_wSeries_of_eventually_mem_span (solution)
