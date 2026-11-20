-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:50:30.895615+00:00
-- url     : https://prove2.me/submissions/1e1d685f-c044-44de-b805-f4ba58eead98

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

section
namespace BinarySketchTruncation.Dev.Prop1
open BinarySketchTruncation.Opposite

lemma map_toReal {S T : Type} [Fintype S] [Fintype T] [DecidableEq T]
    (μ : PMF S) (f : S → T) (t : T) :
    ((μ.map f) t).toReal = ∑ s, (μ s).toReal * (if f s = t then 1 else 0) := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : f s = t
    · simp [h]
    · simp [h, Ne.symm h]
  · intro s _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · simp

lemma joint_mass {n : ℕ} {T : Type} [Fintype T] [DecidableEq T] (p : Bias)
    (G : Vec n × Vec n → T) (t : T) :
    ((((jointLaw n p).map G) t).toReal) =
      ∑ x : Vec n, ((1 : ℝ) / 2 ^ n) *
        ∑ z : Vec n, (cubeLaw n p z).toReal * (if G (x, x + z) = t then 1 else 0) := by
  unfold jointLaw
  rw [PMF.map_bind, PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_mul, PMF.map_comp, map_toReal]
    simp [PMF.uniformOfFintype_apply, Function.comp]
  · intro x _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

lemma add_add_self' {n : ℕ} (x z : Vec n) : x + (x + z) = z := by
  funext i
  have h : x i + x i = 0 := CharTwo.add_self_eq_zero (x i)
  simp [← add_assoc, h]

lemma dom_gen {n : ℕ} {S T : Type} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (p₀ p₁ : Bias) (σ : Vec n → S) (G : Vec n × Vec n → T) (g : S → Vec n → T)
    (e : Vec n → Vec n ≃ Vec n)
    (hG : ∀ x z, G (x, x + z) = g (σ z) (e z x)) :
    Dominates (fun h => (jointLaw n (biasAt p₀ p₁ h)).map (fun xy => σ (xy.1 + xy.2)))
      (fun h => (jointLaw n (biasAt p₀ p₁ h)).map G) := by
  have hn : ((2:ℝ) ^ n) ≠ 0 := by positivity
  refine ⟨fun u t => ((1:ℝ) / 2 ^ n) *
      (Finset.univ.filter (fun w : Vec n => g u w = t)).card, ⟨fun _ _ => by positivity, fun u => ?_⟩, fun h t => ?_⟩
  · rw [← Finset.mul_sum]
    have : ∑ t : T, ((Finset.univ.filter (fun w : Vec n => g u w = t)).card : ℝ) = 2 ^ n := by
      rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
      simp
    rw [this]; field_simp
  · rw [joint_mass]
    simp only [joint_mass]
    simp only [add_add_self']
    have hc : (Fintype.card (Vec n) : ℝ) = 2 ^ n := by simp [Vec, ZMod.card]
    have hk : ∀ u : S, (∑ x : Vec n, (1:ℝ) / 2 ^ n *
        ∑ z : Vec n, (cubeLaw n (biasAt p₀ p₁ h) z).toReal * (if σ z = u then 1 else 0)) =
        ∑ z : Vec n, (cubeLaw n (biasAt p₀ p₁ h) z).toReal * (if σ z = u then 1 else 0) := by
      intro u
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
      field_simp
    have hcard : ∀ s : S, ((Finset.univ.filter (fun w : Vec n => g s w = t)).card : ℝ) =
        ∑ w : Vec n, if g s w = t then (1:ℝ) else 0 := by
      intro s; rw [Finset.card_filter]; push_cast; rfl
    calc _ = ∑ x : Vec n, ∑ z : Vec n, ((1:ℝ) / 2 ^ n *
              (cubeLaw n (biasAt p₀ p₁ h) z).toReal) * (if G (x, x + z) = t then 1 else 0) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
      _ = ∑ z : Vec n, ((1:ℝ) / 2 ^ n * (cubeLaw n (biasAt p₀ p₁ h) z).toReal) *
              ∑ w : Vec n, (if g (σ z) w = t then (1:ℝ) else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [← Finset.mul_sum]
            congr 1
            rw [← (e z).sum_comp (fun w => if g (σ z) w = t then (1:ℝ) else 0)]
            exact Finset.sum_congr rfl fun x _ => by rw [hG]
      _ = _ := by
            simp_rw [hk, Finset.sum_mul, hcard]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ => ?_
            simp_rw [mul_assoc, ite_mul, one_mul, zero_mul, ← Finset.mul_sum]
            simp [Finset.sum_ite_eq]
            ring

end BinarySketchTruncation.Dev.Prop1

namespace BinarySketchTruncation.Opposite
open BinarySketchTruncation.Dev.Prop1

theorem chk_proposition_1 {n kA kB : ℕ} (p₀ p₁ : Bias)
    (A : Matrix (Fin kA) (Fin n) Bit) (B : Matrix (Fin kB) (Fin n) Bit) :
    (∀ x y : Vec n, A.mulVec (x + y) = A.mulVec x + A.mulVec y) ∧
    (∀ x y : Vec n, B.mulVec (x + y) = B.mulVec x + B.mulVec y) ∧
    Dominates (sumSketchExperiment p₀ p₁ A) (sketchExperiment p₀ p₁ A B) ∧
    Dominates (sumSketchExperiment p₀ p₁ B) (sketchExperiment p₀ p₁ A B) := by
  classical
  refine ⟨fun x y => Matrix.mulVec_add _ _ _, fun x y => Matrix.mulVec_add _ _ _, ?_, ?_⟩
  · refine dom_gen p₀ p₁ (fun v => A.mulVec v)
      (fun xy => (A.mulVec xy.1, B.mulVec xy.2))
      (fun u w => (A.mulVec w + u, B.mulVec w)) (fun z => Equiv.addRight z) ?_
    intro x z
    simp only [Equiv.coe_addRight, Matrix.mulVec_add]
    ext1
    · simp only [add_assoc]
      have h : A.mulVec z + A.mulVec z = 0 := by
        funext i; exact CharTwo.add_self_eq_zero _
      simp [h]
    · rfl
  · refine dom_gen p₀ p₁ (fun v => B.mulVec v)
      (fun xy => (A.mulVec xy.1, B.mulVec xy.2))
      (fun v w => (A.mulVec w, B.mulVec w + v)) (fun z => Equiv.refl _) ?_
    intro x z
    simp [Matrix.mulVec_add]

end BinarySketchTruncation.Opposite
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.chk_proposition_1 := @BinarySketchTruncation.Opposite.chk_proposition_1
