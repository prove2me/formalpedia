-- Prove2me | solution 1 for BCFGJPSSV26.FL.alg_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:10:39.690396+00:00
-- url     : https://prove2.me/submissions/c3472a13-8acd-496d-9f69-42a7dc4f321f

module

public import Definitions.Def_BCFGJPSSV26_FL_Run
public import Definitions.Def_BCFGJPSSV26_FL_PolyTime
public import Definitions.Def_BCFGJPSSV26_FL_Main
import all Definitions.Def_BCFGJPSSV26_FL_Main
public import Theorems.Thm_BCFGJPSSV26_FL_lmp_of_score
public import Theorems.Thm_BCFGJPSSV26_FL_runFL_spec
public import Theorems.Thm_BCFGJPSSV26_FL_score_trivialSol_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.FL

open Encoding

variable {I : Instance}

open Greedy in
/-- **The guarantee of the algorithm**: on a valid instance with a client and an opening cost
`f ≥ 0`, a nonempty list of distinct facilities `S` with `cost S ≤ 1.9499 (OPT_f - f |S|)`. -/
theorem alg_spec (hI : I.Valid) (hn : 0 < I.n) {f : ℚ} (hf : 0 ≤ f) :
    I.IsCenterList (alg (toRaw I) f) ∧
      I.cost (I.centers (alg (toRaw I) f)) ≤
        1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (alg (toRaw I) f).length) := by
  obtain ⟨O, hO, hopt⟩ := exists_optFL hI (f : ℝ)
  have hcase : (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤ (lmpC : ℝ) * I.optFL f ∨
      (I.IsCenterList (runFL (toRaw I) f) ∧
        (score (toRaw I) f (runFL (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * I.optFL f) := by
    by_cases hT : (trivialSol (toRaw I)).length ≤ O.card ∨ f = 0
    · exact .inl (score_trivialSol_le hI hn hf hO hopt hT)
    · push Not at hT
      obtain ⟨hTO, hf0⟩ := hT
      have hO1 : 1 ≤ O.card := Finset.card_pos.2 hO
      have hn2 : 2 ≤ I.n := by
        have := trivialSol_length_le_n (I := I)
        omega
      have hm2 : 2 ≤ I.m := by
        have := trivialSol_length_le_m hI
        omega
      have hc : 0 < I.cost O := lt_of_le_of_ne (Instance.cost_nonneg' hI O) fun h ↦
        absurd (trivialSol_length_le_card hI hO h.symm) (not_le.2 hTO)
      have hfpos : 0 < f := lt_of_le_of_ne hf (Ne.symm hf0)
      obtain ⟨h1, h2⟩ := runFL_spec hI hn2 hm2 hfpos hO hc
      exact .inr ⟨h1, by rw [hopt]; exact h2⟩
  have h := alg_spec_of hI hn f hcase
  exact ⟨h.1, lmp_of_score h.1 h.2⟩

end BCFGJPSSV26.FL

end

public section

theorem solution : type_of% @BCFGJPSSV26.FL.alg_spec := @BCFGJPSSV26.FL.alg_spec
