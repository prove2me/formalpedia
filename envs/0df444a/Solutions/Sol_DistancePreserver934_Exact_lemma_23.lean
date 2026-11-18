-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_23
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:05:25.058573+00:00
-- url     : https://prove2.me/submissions/3c67ffd4-7498-42a1-92c6-ae92918faf8f

import Theorems.Thm_DistancePreserver934_Exact_observation_20
import Definitions.Def_DistancePreserver934_Exact_Removal

set_option autoImplicit false
open Classical DistancePreserver934.Exact

private lemma self_minimal {V : Type} [Fintype V] (G K : SimpleGraph V)
    (R : Finset (Sym2 V)) (hK : IsMinimalPreserver G K R) : IsMinimalPreserver K K R := by
  refine ⟨⟨le_rfl, by simp⟩, ?_⟩
  intro e he hdel
  apply hK.2 e he
  exact ⟨hdel.1.trans hK.1.1, fun s t hst => (hdel.2 s t hst).trans (hK.1.2 s t hst)⟩

private lemma demand_transfer {V : Type} [Fintype V] (G K : SimpleGraph V)
    (P R : Finset (Sym2 V)) (hP : IsDemandSet G P) (hR : R ⊆ P)
    (hK : IsMinimalPreserver G K R) : IsDemandSet K R := by
  intro s t hst
  refine ⟨(hP s t (hR hst)).1, ?_⟩
  apply SimpleGraph.edist_ne_top_iff_reachable.mp
  rw [hK.1.2 s t hst]
  exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hP s t (hR hst)).2

private lemma current_preserver {V : Type} [Fintype V] (G K K' : SimpleGraph V)
    (R R' : Finset (Sym2 V)) (hK : IsMinimalPreserver G K R)
    (hR : R' ⊆ R) (hup : IsUpdate G K K' R') : IsPreserver K K' R' := by
  refine ⟨hup.1, fun s t hst => ?_⟩
  rw [hup.2.1.2 s t hst, hK.1.2 s t (hR hst)]

private lemma run_inv {V : Type} [Fintype V] (c₀ c₁ c₂ : ℝ) (G H : SimpleGraph V)
    (P : Finset (Sym2 V)) (hH : IsMinimalPreserver G H P)
    (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind)
    (hrun : IsRun c₀ c₁ c₂ G H P τ st kind) :
    ∀ i ≤ τ, IsMinimalPreserver G (st i).1 (st i).2 ∧ (st i).2 ⊆ P ∧
      (st i).2.card + i ≤ P.card := by
  intro i hi
  induction i with
  | zero => simpa [hrun.1] using And.intro hH (And.intro (le_refl P) (le_refl P.card))
  | succ i ih =>
    obtain ⟨hKi,hRi,hci⟩ := ih (by omega)
    rcases hrun.2 i (by omega) with ⟨hk,hs⟩ | ⟨hk,hs⟩
    · obtain ⟨hp,q,hq,hl,hR',hup⟩ := hs
      refine ⟨hup.2, ?_, ?_⟩
      · rw [hR']
        exact (Finset.erase_subset _ _).trans hRi
      · have hc : (st (i+1)).2.card + 1 = (st i).2.card := by
          rw [hR']; exact Finset.card_erase_add_one hq
        omega
    · obtain ⟨hp,hl,Q,S,hQR,hQ,hS,hcov,hlarge,hsmall,hdiam,hR',hup⟩ := hs
      refine ⟨hup.2, ?_, ?_⟩
      · rw [hR']
        exact Finset.sdiff_subset.trans hRi
      · have hc := Finset.card_sdiff_add_card_eq_card hQR
        have hqpos := Finset.card_pos.mpr hQ
        rw [hR']
        omega

theorem solution {V : Type} [Fintype V] (c₀ c₁ c₂ C : ℝ) (G H : SimpleGraph V)
    (P : Finset (Sym2 V)) (hset : Sec6Setting C G H P)
    (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind)
    (hrun : IsRun c₀ c₁ c₂ G H P τ st kind) :
    kindLoss τ st kind StepKind.one ≤ sec6n V * sec6d H / 5 := by
  classical
  have hstate := run_inv c₀ c₁ c₂ G H P hset.2.1 τ st kind hrun
  have hτ : τ ≤ P.card := by have := (hstate τ le_rfl).2.2; omega
  have hl : 0 ≤ sec6l H P := by
    dsimp [sec6l, sec6d, sec6n]
    positivity
  have hp : 0 < (P.card : ℝ) := (Real.rpow_nonneg (by dsimp [sec6n]; positivity) _).trans_lt hset.2.2.1
  have hstep : ∀ i ∈ (Finset.range τ).filter (fun i => kind i = StepKind.one),
      stepLoss st i ≤ sec6l H P := by
    intro i hi
    obtain ⟨hir,hkind⟩ := Finset.mem_filter.mp hi
    have hiτ := Finset.mem_range.mp hir
    obtain ⟨hKi,hRi,_⟩ := hstate i hiτ.le
    have hs : Step1 G H P (st i) (st (i+1)) := by
      rcases hrun.2 i hiτ with ⟨hk,hs⟩ | ⟨hk,hs⟩
      · exact hs
      · rw [hkind] at hk; cases hk
    obtain ⟨hp',q,hq,hlq,hR',hup⟩ := hs
    have hR : IsDemandSet (st i).1 (st i).2 := demand_transfer G (st i).1 P (st i).2 hset.1 hRi hKi
    have hself := self_minimal G (st i).1 (st i).2 hKi
    have hcur : IsPreserver (st i).1 (st (i+1)).1 ((st i).2.erase q) := by
      rw [← hR']
      exact current_preserver G (st i).1 (st (i+1)).1 (st i).2 (st (i+1)).2 hKi
        (by rw [hR']; exact Finset.erase_subset _ _) hup
    have hob := DistancePreserver934.Exact.observation_20 (st i).1 (st i).2 hR hself q hq (st (i+1)).1 hcur
    have hcost : stepLoss st i ≤ (privLen (st i).1 (st i).2 q : ℝ) := by
      dsimp [stepLoss]
      exact_mod_cast hob.2
    exact hcost.trans hlq
  calc
    kindLoss τ st kind StepKind.one ≤
        ∑ _i ∈ (Finset.range τ).filter (fun i => kind i = StepKind.one), sec6l H P :=
      Finset.sum_le_sum hstep
    _ = (((Finset.range τ).filter (fun i => kind i = StepKind.one)).card : ℝ)*sec6l H P := by simp
    _ ≤ (τ : ℝ)*sec6l H P := by
      apply mul_le_mul_of_nonneg_right _ hl
      exact_mod_cast (Finset.card_filter_le (Finset.range τ) (fun i => kind i = StepKind.one)).trans_eq (Finset.card_range τ)
    _ ≤ (P.card : ℝ)*sec6l H P := mul_le_mul_of_nonneg_right (by exact_mod_cast hτ) hl
    _ = sec6n V * sec6d H / 5 := by
      dsimp [sec6l]
      field_simp
