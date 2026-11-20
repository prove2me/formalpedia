-- Prove2me | solution 1 for EF104SmallSuffixChains__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T15:23:31.729929+00:00
-- url     : https://prove2.me/submissions/38282a79-103d-40cf-8275-0f8611988f1f

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
import Theorems.Thm_EF104ContinuousSuffixSweep__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
import Theorems.Thm_FiniteContinuousCommonSubdivision__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ι → ℕ) (D : ι → ℕ → Set ℝ),
    ∀ j ∈ N,
      D j 0 = ∅ ∧ D j (m j) = (P j).toSet ∧
      (∀ k ≤ m j, IsSuffix (D j k) (P j)) ∧
      ∀ k < m j, D j k ⊆ D j (k + 1) ∧
        ∀ i ∈ N, 0 ≤ (V i).value (D j (k + 1)) - (V i).value (D j k) ∧
          (V i).value (D j (k + 1)) - (V i).value (D j k) ≤ δ := by
  classical
  have hex : ∀ j : ι, ∃ (m : ℕ) (D : ℕ → Set ℝ), j ∈ N →
      D 0 = ∅ ∧ D m = (P j).toSet ∧
      (∀ k ≤ m, IsSuffix (D k) (P j)) ∧
      ∀ k < m, D k ⊆ D (k + 1) ∧
        ∀ i ∈ N, 0 ≤ (V i).value (D (k + 1)) - (V i).value (D k) ∧
          (V i).value (D (k + 1)) - (V i).value (D k) ≤ δ := by
    intro j
    by_cases hj : j ∈ N
    · obtain ⟨S, hS0, hS1, hSs, hSm, hSv⟩ :=
        EF104ContinuousSuffixSweep__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1 (P j) (hP j hj)
      obtain ⟨m, t, _hm, ht0, htm, htr, hto, htv⟩ :=
        FiniteContinuousCommonSubdivision__p2m_99142f0d_48c1_4bba_8593_cef73a2796b8_a1
          (fun i x ↦ (V i).value (S x)) N
          (fun i _hi ↦ (hSv (V i)).1) δ hδ
      refine ⟨m, (fun k ↦ S (t k)), ?_⟩
      intro _hj
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [ht0] using hS0
      · simpa only [htm] using hS1
      · intro k hk
        exact hSs (t k) (htr k hk)
      · intro k hk
        have hk0 := htr k (Nat.le_of_lt hk)
        have hk1 := htr (k + 1) (Nat.succ_le_of_lt hk)
        refine ⟨hSm hk0 hk1 (hto k hk), ?_⟩
        intro i hi
        constructor
        · exact sub_nonneg.mpr ((hSv (V i)).2 hk0 hk1 (hto k hk))
        · exact le_trans (le_abs_self _) (htv k hk i hi)
    · refine ⟨0, (fun _ ↦ ∅), ?_⟩
      intro hj'
      exact False.elim (hj hj')
  choose m D h using hex
  exact ⟨m, D, h⟩

