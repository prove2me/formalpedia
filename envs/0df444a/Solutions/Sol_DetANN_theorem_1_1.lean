-- Prove2me | solution 1 for DetANN.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-21T08:47:08.38989+00:00
-- url     : https://prove2.me/submissions/960751f3-f16b-4c36-95b9-e787dc869a94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split
import Theorems.Thm_DetANN_lemma_3_3
import Theorems.Thm_DetANN_theorem_1_1_correctness
import Theorems.Thm_DetANN_Thm11_outer_composition

namespace DetANN

namespace Thm11Top

/-- A structure whose answers are local answers is a `(1 + ε)`-ANN structure, by
`theorem_1_1_correctness`. -/
lemma ann_of_local (C₀s : ℝ)
    (hcor : ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ (d n k : ℕ), d ≤ 2 ^ k →
      ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∀ (q : EuclideanSpace ℝ (Fin d)) (x : Fin (2 ^ k) → Fin n),
            LocalGuarantee (annBlocks C₀ k P ε) (annTuples k ε) (paddedSet k P)
                (padVec (2 ^ k) q) (fun v => padVec (2 ^ k) (P (x v))) (1 + ε / 100) →
              ∃ v, ∀ i, ‖q - P (x v)‖ ≤ (1 + ε) * ‖q - P i‖)
    (Pre Qry : PNormReg.Program) (d n k : ℕ) (hk : d ≤ 2 ^ k) (C₀ : ℝ) (hC₀ : C₀s ≤ C₀)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (hP : Function.Injective P) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (T S U : ℝ)
    (h : Thm11.IsDetStructure Pre Qry P ε (Thm11.LocalAnswer C₀ k P ε) T S U) :
    IsDetANNStructure Pre Qry P ε (1 + ε) T S U := by
  obtain ⟨t, h1, h2, h3, h4⟩ := h
  refine ⟨t, h1, h2, h3, fun q => ?_⟩
  obtain ⟨t', g1, g2, a, g3, x, hx, hax⟩ := h4 q
  refine ⟨t', g1, g2, a, g3, fun j => ?_⟩
  obtain ⟨v, hv⟩ := hcor C₀ hC₀ d n k hk P hP ε hε hε1 q x hx
  exact (hax v).trans (hv j)

end Thm11Top

theorem _root_.solution :
    ∃ Pre Qry : PNormReg.Program, DetProgram Pre ∧ DetProgram Qry ∧
      ∃ C K : ℕ, ∀ d n : ℕ, 1 ≤ d → d ≤ n →
        ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            IsDetANNStructure Pre Qry P ε (1 + ε)
              ((C : ℝ) * (n : ℝ) ^ ((K : ℝ) * ε⁻¹ ^ K))
              ((C : ℝ) * (n : ℝ) ^ ((K : ℝ) * ε⁻¹ ^ K))
              ((C : ℝ) * ((d : ℝ) ^ 2 + d * ε⁻¹ ^ K * (1 + Real.log n) ^ K)) := by
  obtain ⟨Pre₃, Qry₃, hD1, hD2, C, hC, K, C', h33⟩ := lemma_3_3
  obtain ⟨C₀s, hC₀s, hcor⟩ := theorem_1_1_correctness
  obtain ⟨Pre, Qry, hP1, hP2, Cm, Km, hA⟩ :=
    Thm11.outer_composition Pre₃ Qry₃ hD1 hD2 C K C' hC h33 C₀s hC₀s
  refine ⟨Pre, Qry, hP1, hP2, Cm, Km, fun d n hd hdn P hP ε hε hε1 => ?_⟩
  obtain ⟨k, C₀, hk, hC₀, hS⟩ := hA d n hd hdn P hP ε hε hε1
  exact Thm11Top.ann_of_local C₀s hcor Pre Qry d n k hk C₀ hC₀ P hP ε hε hε1 _ _ _ hS

end DetANN
