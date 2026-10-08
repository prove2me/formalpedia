-- Prove2me | solution 1 for ConstrainedQueueing.Nonstationary.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:45:09.169023+00:00
-- url     : https://prove2.me/submissions/a3a00166-c147-42cd-a193-820017f96d2d

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model

open ConstrainedQueueing.Nonstationary
open Set Filter
open scoped Topology

private theorem coS_bounds {L N : ℕ} (net : Network L N) {c : Fin N → ℝ}
    (hc : c ∈ coS net) : 0 ≤ c ∧ c ≤ 1 := by
  have hs : coS net ⊆ Set.Icc (0 : Fin N → ℝ) 1 := by
    apply convexHull_min
    · rintro _ ⟨s, _, rfl⟩
      constructor <;> intro i <;> simp only [ConstrainedQueueing.MaxThroughput.actVec]
      all_goals split_ifs <;> norm_num
    · exact convex_Icc _ _
  exact hs hc

private theorem region_closed {L N : ℕ} (net : Network L N) :
    IsClosed {a : Fin L → ℝ | 0 ≤ a ∧ ∃ f, IsAdmissibleFlow net a f ∧ ∃ c ∈ coS net, f ≤ c} := by
  let R : (Fin N → ℝ) → (Fin L → ℝ) := fun f => -((routing net).mulVec f)
  have hR : Continuous R := by
    dsimp [R]
    fun_prop
  have hco : IsCompact (coS net) := (Set.toFinite _).isCompact_convexHull ℝ
  let T : Set ((Fin N → ℝ) × (Fin N → ℝ)) :=
    {u | u.1 ∈ Set.Icc 0 1 ∧ u.2 ∈ coS net ∧ u.1 ≤ u.2 ∧ 0 ≤ R u.1}
  have hT : IsCompact T := by
    have hb := (isCompact_Icc : IsCompact (Set.Icc (0 : Fin N → ℝ) 1)).prod hco
    have hc : IsClosed {u : (Fin N → ℝ) × (Fin N → ℝ) | u.1 ≤ u.2 ∧ 0 ≤ R u.1} :=
      (isClosed_le continuous_fst continuous_snd).inter
        (isClosed_le continuous_const (hR.comp continuous_fst))
    have he : T = (Set.Icc (0 : Fin N → ℝ) 1 ×ˢ coS net) ∩
        {u : (Fin N → ℝ) × (Fin N → ℝ) | u.1 ≤ u.2 ∧ 0 ≤ R u.1} := by
      ext u
      simp [T, and_assoc]
    rw [he]
    exact hb.inter_right hc
  have he : R '' Prod.fst '' T =
      {a : Fin L → ℝ | 0 ≤ a ∧ ∃ f, IsAdmissibleFlow net a f ∧ ∃ c ∈ coS net, f ≤ c} := by
    ext a
    constructor
    · rintro ⟨f, ⟨⟨f', c⟩, hu, rfl⟩, rfl⟩
      exact ⟨hu.2.2.2, f', ⟨hu.1.1, rfl⟩, c, hu.2.1, hu.2.2.1⟩
    · rintro ⟨ha, f, ⟨hf, rfl⟩, c, hc, hfc⟩
      refine ⟨f, ⟨(f, c), ?_, rfl⟩, rfl⟩
      exact ⟨⟨hf, hfc.trans (coS_bounds net hc).2⟩, hc, hfc, ha⟩
  rw [← he]
  exact ((hT.image continuous_fst).image hR).isClosed

theorem solution {L N : ℕ} (net : Network L N) :
    closure (Cprime net) =
      {a : Fin L → ℝ | 0 ≤ a ∧ ∃ f, IsAdmissibleFlow net a f ∧ ∃ c ∈ coS net, f ≤ c} := by
  apply le_antisymm
  · apply closure_minimal _ (region_closed net)
    rintro a ⟨ha, f, hf, c, hc, hstrict⟩
    refine ⟨ha, f, hf, c, hc, fun i => ?_⟩
    by_cases hfi : 0 < f i
    · exact (hstrict i).1 hfi |>.le
    · have hzero : f i = 0 := le_antisymm (le_of_not_gt hfi) (hf.1 i)
      rw [hzero]
      exact (coS_bounds net hc).1 i
  · rintro a ⟨ha, f, hf, c, hc, hfc⟩
    let b : ℝ → (Fin L → ℝ) := fun t => t • a
    have hb : Continuous b := by fun_prop
    have hmem : ∀ t ∈ Set.Ico (0 : ℝ) 1, b t ∈ Cprime net := by
      rintro t ⟨ht0, ht1⟩
      refine ⟨smul_nonneg ht0 ha, t • f, ⟨smul_nonneg ht0 hf.1, ?_⟩, c, hc, ?_⟩
      · change t • a = -(routing net).mulVec (t • f)
        rw [hf.2]
        simp [Matrix.mulVec_smul, smul_neg]
      · intro i
        constructor
        · intro hpos
          have hfpos : 0 < f i := by
            change 0 < t * f i at hpos
            nlinarith [hf.1 i]
          change t * f i < c i
          nlinarith [hfc i]
        · intro hci
          have hfzero : f i = 0 := le_antisymm (hci ▸ hfc i) (hf.1 i)
          simp [hfzero]
    have hcl : b 1 ∈ closure (Cprime net) := by
      apply closure_mono (show b '' Set.Ico (0 : ℝ) 1 ⊆ Cprime net from by
        rintro _ ⟨t, ht, rfl⟩; exact hmem t ht)
      apply image_closure_subset_closure_image hb
      have h1 : (1 : ℝ) ∈ closure (Set.Ico (0 : ℝ) 1) := by
        rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
        simp
      exact ⟨1, h1, rfl⟩
    simpa [b] using hcl

#print axioms solution
