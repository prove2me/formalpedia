-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_prep_oracle_v4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T05:38:24.986737+00:00
-- url     : https://prove2.me/submissions/b0e40545-a3cb-4b96-9082-5edd527991b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000
import Theorems.Thm_DetDLP_scalar_contraction_local_prep_oracle_budget_witness_v4

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

lemma polyBound_le_of_le {a b u : ℕ} (hab : a ≤ b) : polyBound a u ≤ polyBound b u := by
  dsimp [polyBound]
  have hbase : (1 : ℝ) ≤ (u : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 u
  have hpow : ((u : ℝ) + 1) ^ a ≤ ((u : ℝ) + 1) ^ b :=
    pow_le_pow_right₀ hbase (by exact_mod_cast hab)
  have ha : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hnn : 0 ≤ ((u : ℝ) + 1) ^ a :=
    pow_nonneg (add_nonneg (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)) _
  nlinarith

lemma two_rpow_le {x y : ℝ} (hxy : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) hxy

lemma prep_space_mono {cap K0 K u : ℕ} (hK : K0 ≤ K)
    (h : cap ≤ K0 * (u + 1) ^ K0) : cap ≤ K * (u + 1) ^ K := by
  refine h.trans (Nat.mul_le_mul hK ?_)
  exact Nat.pow_le_pow_right (Nat.le_add_left 1 u) hK

lemma prep_time_mono {steps K0 K u Told : ℕ} {expr : ℝ}
    (hK : K0 ≤ K) (hexpr : 0 ≤ expr)
    (h : (steps : ℝ) ≤ polyBound K0 u * (Told : ℝ) * (2 : ℝ) ^ ((K0 : ℝ) * expr)) :
    (steps : ℝ) ≤ polyBound K u * (Told : ℝ) * (2 : ℝ) ^ ((K : ℝ) * expr) := by
  refine h.trans ?_
  have hpoly := polyBound_le_of_le (u := u) hK
  have hexp : (2 : ℝ) ^ ((K0 : ℝ) * expr) ≤ (2 : ℝ) ^ ((K : ℝ) * expr) :=
    two_rpow_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hexpr)
  have hT : 0 ≤ (Told : ℝ) := Nat.cast_nonneg _
  have hp0 : 0 ≤ polyBound K0 u := by
    dsimp [polyBound]
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (add_nonneg (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)) _)
  have he0 : 0 ≤ (2 : ℝ) ^ ((K0 : ℝ) * expr) := Real.rpow_nonneg (by norm_num) _
  have h1 : polyBound K0 u * (Told : ℝ) ≤ polyBound K u * (Told : ℝ) :=
    mul_le_mul_of_nonneg_right hpoly hT
  have h2 :
      polyBound K0 u * (Told : ℝ) * (2 : ℝ) ^ ((K0 : ℝ) * expr) ≤
        polyBound K u * (Told : ℝ) * (2 : ℝ) ^ ((K0 : ℝ) * expr) :=
    mul_le_mul_of_nonneg_right h1 he0
  have h3 :
      polyBound K u * (Told : ℝ) * (2 : ℝ) ^ ((K0 : ℝ) * expr) ≤
        polyBound K u * (Told : ℝ) * (2 : ℝ) ^ ((K : ℝ) * expr) :=
    mul_le_mul_of_nonneg_left hexp (mul_nonneg (le_trans hp0 hpoly) hT)
  exact le_trans h2 h3

/-- Lift one oracle degree to every external budget `L` by monotonicity of the bounds. -/
theorem solution
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov) :
    ∃ (s lp : ℕ) (hs : 0 < s) (prep : BitProgram.Program 8 (20 + s) lp),
      ∀ L : ℕ, ∃ K : ℕ,
        ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
          (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
          2 ≤ β → 1 ≤ Told → G.nE ≤ C * β → G.nV ≤ β ^ c0 →
          1 ≤ P → P ≤ C * β → 1 ≤ ℓ' → ℓ' ≤ C * β →
          (∀ v t i, A v t i < 2 ^ P) →
          (∀ v t (regs : Fin 3 → Bool),
            let q := (encodePortQuery desc v.val (List.ofFn t)).tail
            let start : BitProgram.Cfg 3 se le := ⟨some Q.entry, regs, fun j =>
              if j = it then List.replicate q.length true else if j = iv then q else []⟩
            ∃ (n : ℕ) (c : BitProgram.Cfg 3 se le), n ≤ 8 * Told ∧ BitProgram.Trace Q n start c ∧
              c.pc = none ∧ ((((c.stacks ot).zip (c.stacks ov)).takeWhile Prod.fst).map Prod.snd) =
                encodeNatListBin (List.ofFn (A v t)) ∧
              ∀ j b, j ≤ n → BitProgram.Trace Q j start b →
                ∀ i, (b.stacks i).length ≤ (β + desc.length) ^ c0 + 8) →
          let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
          let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
          let expr : ℝ :=
            (β : ℝ) / Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ + 1),
              ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d)
          let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
            Polynomial.monomial i.val (A v t i : ℤ))
          let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
            ((Z.coeff i.val : ZMod (2 ^ P)).val))
          let word := w.foldr (fun b z => b.toNat + 2 * z) 1
          let context : Fin s → List Bool := fun i => if i.val = 0 then word.bits else []
          let reg : Fin 8 → Bool := fun _ => true
          let qn := word + 2
          let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
            let v : Fin 12 → ℕ := ![qn, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
            Fin.addCases (m := 20) (n := s)
              (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
          let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
          ∃ (prepSteps cap0 U : ℕ),
            (∀ i, (context i).length ≤ U) ∧
            BitProgram.Trace prep prepSteps start ⟨none, reg, pack 0 0 1 0 0 0⟩ ∧
            (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c →
              ∀ i, (c.stacks i).length ≤ cap0) ∧
            ((prepSteps : ℕ) : ℝ) ≤
              polyBound K (β + desc.length) * (Told : ℝ) * (2 : ℝ) ^ ((K : ℝ) * expr) ∧
            cap0 ≤ K * (β + desc.length + 1) ^ K := by
  obtain ⟨s, lp, hs, prep, K0, h0⟩ :=
    scalar_contraction_local_prep_oracle_budget_witness_v4 C c0 hC hc0 Q it iv ot ov hi ho
  refine ⟨s, lp, hs, prep, ?_⟩
  intro L
  refine ⟨max K0 (L + 1), ?_⟩
  intro β P ℓ' Told desc G A hβ ht he hv hP₁ hP₂ hl₁ hl₂ ha hQ
  have hK0 : K0 ≤ max K0 (L + 1) := le_max_left _ _
  obtain ⟨prepSteps, cap0, U, hU, hTrace, hcap, htime, hspace⟩ :=
    h0 β P ℓ' Told desc G A hβ ht he hv hP₁ hP₂ hl₁ hl₂ ha hQ
  refine ⟨prepSteps, cap0, U, hU, hTrace, hcap, ?_, ?_⟩
  · refine prep_time_mono (K0 := K0) (K := max K0 (L + 1)) hK0 ?_ htime
    apply add_nonneg
    · exact div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    · refine Finset.sum_nonneg ?_
      intro d _
      exact div_nonneg
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) _))
        (Real.sqrt_nonneg _)
  · exact prep_space_mono (K0 := K0) (K := max K0 (L + 1)) hK0 hspace
