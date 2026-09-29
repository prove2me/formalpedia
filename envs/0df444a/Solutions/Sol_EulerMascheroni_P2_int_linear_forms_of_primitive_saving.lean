-- Prove2me | solution 1 for EulerMascheroni.P2.int_linear_forms_of_primitive_saving
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T19:45:00.839115+00:00
-- url     : https://prove2.me/submissions/f2847256-bd9f-464d-8d86-0720da6c437a

import Definitions.Def_eulerMascheroni_p2PrimitiveNormalization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
open Filter Topology
open EulerMascheroni.P2

namespace P2PrimitiveBridgeProof
lemma normalization (n : ℕ) (hQ : 0 < Q n) :
    0 < primitiveQ n ∧ 0 < primitiveScale n ∧
    (primitiveQ n : ℝ) = primitiveScale n * (Q n : ℝ) ∧
    (primitiveP n : ℝ) = primitiveScale n * (P n : ℝ) := by
  have hqr : (0 : ℝ) < (Q n : ℝ) := by exact_mod_cast hQ
  have hd : 0 < primitiveQ n := (P n / Q n).pos
  have hnum : (primitiveP n : ℝ) / (primitiveQ n : ℝ) =
      (P n : ℝ) / (Q n : ℝ) := by
    exact_mod_cast (Rat.num_div_den (P n / Q n))
  refine ⟨hd, div_pos (by exact_mod_cast hd) hqr, ?_, ?_⟩
  · dsimp [primitiveScale]
    field_simp
  · dsimp [primitiveScale]
    have hdr : (primitiveQ n : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp at hnum ⊢
    nlinarith

end P2PrimitiveBridgeProof

open P2PrimitiveBridgeProof

theorem solution
    (hQ : ∀ n, 0 < Q n)
    (hnum : Tendsto (fun n : ℕ => F (n+1) / fModel (n+1) - Real.sin (phase (n+1)))
      atTop (nhds 0))
    (hsave : PrimitiveSaving) :
    ∃ p q : ℕ → ℤ, (∀ n, 0 < q n) ∧
      (∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0) ∧
      Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
        atTop (nhds 0) := by
  classical
  let v : ℕ → ℝ := fun n => F (n+1) / fModel (n+1) - Real.sin (phase (n+1))
  have hv : Tendsto v atTop (nhds 0) := hnum
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (hv.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1/4)))
  have hchoose : ∀ k : ℕ, ∃ n : ℕ, M+k ≤ n ∧
      (1/2 : ℝ) ≤ |Real.sin (phase (n+1))| ∧
      primitiveScale (n+1) * fModel (n+1) < 1 / ((k : ℝ)+1) := by
    intro k
    exact hsave _ (by positivity) (M+k)
  choose ns hns hphase hsmall using hchoose
  let p : ℕ → ℤ := fun k => primitiveP (ns k+1)
  let q : ℕ → ℤ := fun k => primitiveQ (ns k+1)
  let L : ℕ → ℝ := fun k => (q k : ℝ)*Real.eulerMascheroniConstant-(p k : ℝ)
  have hfm (n : ℕ) : 0 < fModel (n+1) := by
    have hs : 0 < scale (n+1) := by unfold scale; positivity
    unfold fModel
    positivity
  have hL (k : ℕ) : L k = (primitiveScale (ns k+1) * fModel (ns k+1)) *
      (Real.sin (phase (ns k+1)) + v (ns k)) := by
    obtain ⟨_,_,hq,hp⟩ := normalization (ns k+1) (hQ _)
    dsimp [L,p,q]
    push_cast
    rw [hq,hp]
    dsimp [v]
    unfold F
    field_simp [(hfm (ns k)).ne']
    <;> ring
  have hnonzero : ∀ k, L k ≠ 0 := by
    intro k
    have hvk : |v (ns k)| < 1/4 := hM _ (by have := hns k; omega)
    have hs : Real.sin (phase (ns k+1)) + v (ns k) ≠ 0 := by
      intro he
      have hh : Real.sin (phase (ns k+1)) = -v (ns k) := by linarith
      have hp := hphase k
      rw [hh,abs_neg] at hp
      linarith
    rw [hL]
    exact mul_ne_zero (mul_ne_zero (normalization _ (hQ _)).2.1.ne' (hfm _).ne') hs
  have hlim : Tendsto L atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun k : ℕ => 2*(1/((k:ℝ)+1)))
    · intro k
      rw [Real.norm_eq_abs,hL,abs_mul]
      have hc := (normalization (ns k+1) (hQ _)).2.1
      have hf := hfm (ns k)
      rw [abs_of_pos (mul_pos hc hf)]
      have hvk : |v (ns k)| < 1/4 := hM _ (by have := hns k; omega)
      have ha := abs_add_le (Real.sin (phase (ns k+1))) (v (ns k))
      have hb := Real.abs_sin_le_one (phase (ns k+1))
      have hs := hsmall k
      calc
        _ ≤ (primitiveScale (ns k+1) * fModel (ns k+1)) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (mul_pos hc hf))
        _ ≤ _ := by linarith
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  refine ⟨p,q,?_,hnonzero,hlim⟩
  intro k
  dsimp [q]
  exact_mod_cast (normalization (ns k+1) (hQ _)).1

