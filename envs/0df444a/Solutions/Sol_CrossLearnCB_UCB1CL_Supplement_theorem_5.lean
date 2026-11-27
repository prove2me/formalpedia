-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:07.550636+00:00
-- url     : https://prove2.me/submissions/f7168932-5920-45f6-b71e-9a370519514e

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_GraphLowerQuantities
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

open CrossLearnCB
open CrossLearnCB.UCB1CL
open CrossLearnCB.UCB1CL.Supplement

/-- Theorem 5, p. 27. An absolute positive lower-bound constant, with sufficiently large
horizon for each fixed graph and arm count. All arms have graph G. -/
theorem solution : ∃ c : ℝ, 0 < c ∧
    ∀ (K C : ℕ) [NeZero K], 2 ≤ K → 0 < C → ∀ G : Fin C → Fin C → Prop,
    (∀ d, G d d) → ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
    ∃ D : Fin C → ℝ, IsDistribution D ∧ ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
      ∃ S : StochInstance K C, S.IsCoordinateIndependent ∧ S.D = D ∧
        c * Real.sqrt (nuTwo G * K * T) ≤ stochRegret T (fun _ => G) S A := by
          classical
          have hGraph : ∀ (C : ℕ), 0 < C → ∀ G : Fin C → Fin C → Prop,
              (∀ d, G d d) → 1 ≤ nuTwo G ∧ nuTwo G ≤ C := by
            intro C hC G hG
            let Q : (Fin C → ℝ) → Fin C → ℝ :=
              fun f c => ∑ d ∈ Finset.univ.filter (fun d => G d c), f d
            let W : (Fin C → ℝ) → ℝ := fun f => ∑ c, f c / Real.sqrt (Q f c)
            have hQ : ∀ f : Fin C → ℝ, (∀ c, 0 ≤ f c) → ∀ c, f c ≤ Q f c := by
              intro f hf c
              apply Finset.single_le_sum (fun d _ => hf d)
              simp [Q, hG c]
            have hW : ∀ f : Fin C → ℝ, (∀ c, 0 ≤ f c) → (∑ c, f c) = 1 →
                W f ^ 2 ≤ C := by
              intro f hf hsum
              have hterm : ∀ c, f c / Real.sqrt (Q f c) ≤ Real.sqrt (f c) := by
                intro c
                by_cases hc : f c = 0
                · simp [hc]
                · have hfc : 0 < f c := lt_of_le_of_ne (hf c) (Ne.symm hc)
                  have hqc : 0 < Q f c := lt_of_lt_of_le hfc (hQ f hf c)
                  apply (div_le_iff₀ (Real.sqrt_pos.2 hqc)).2
                  calc
                    f c = Real.sqrt (f c) * Real.sqrt (f c) := (Real.mul_self_sqrt (hf c)).symm
                    _ ≤ Real.sqrt (f c) * Real.sqrt (Q f c) :=
                      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQ f hf c)) (Real.sqrt_nonneg _)
              have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
                (fun c : Fin C => Real.sqrt (f c)) (fun _ : Fin C => (1 : ℝ))
              have hsqr : (∑ c, Real.sqrt (f c)) ^ 2 ≤ C := by
                simpa [Real.sq_sqrt, hf, hsum] using hcs
              have hWnonneg : 0 ≤ W f := Finset.sum_nonneg fun c _ =>
                div_nonneg (hf c) (Real.sqrt_nonneg _)
              have hsumle : W f ≤ ∑ c, Real.sqrt (f c) := Finset.sum_le_sum fun c _ => hterm c
              nlinarith [Finset.sum_nonneg (fun c (_ : c ∈ Finset.univ) => Real.sqrt_nonneg (f c))]
            have hbdd : BddAbove {x : ℝ | ∃ f : Fin C → ℝ, (∀ c, 0 ≤ f c) ∧ (∑ c, f c) = 1 ∧
                x = W f ^ 2} := by
              refine ⟨C, ?_⟩
              rintro x ⟨f, hf, hsum, rfl⟩
              exact hW f hf hsum
            let c₀ : Fin C := ⟨0, hC⟩
            let f₀ : Fin C → ℝ := fun c => if c = c₀ then 1 else 0
            have hf₀ : ∀ c, 0 ≤ f₀ c := by intro c; simp [f₀]; split_ifs <;> norm_num
            have hsum₀ : (∑ c, f₀ c) = 1 := by simp [f₀]
            have hQ₀ : Q f₀ c₀ = 1 := by simp [Q, f₀, hG c₀]
            have hW₀ : W f₀ = 1 := by
              change (∑ c, f₀ c / Real.sqrt (Q f₀ c)) = 1
              rw [Finset.sum_eq_single c₀]
              · rw [show f₀ c₀ = 1 by simp [f₀], hQ₀]
                norm_num
              · intro b hb hbne
                simp [f₀, hbne]
              · simp
            have hone : (1 : ℝ) ∈ {x : ℝ | ∃ f : Fin C → ℝ, (∀ c, 0 ≤ f c) ∧
                (∑ c, f c) = 1 ∧ x = W f ^ 2} := by
              exact ⟨f₀, hf₀, hsum₀, by rw [hW₀]; norm_num⟩
            constructor
            · exact le_csSup hbdd hone
            · exact csSup_le ⟨1, hone⟩ (by rintro x ⟨f, hf, hs, rfl⟩; exact hW f hf hs)
          have hApprox : ∀ (C : ℕ), 0 < C → ∀ G : Fin C → Fin C → Prop,
              (∀ d, G d d) → ∃ D : Fin C → ℝ, IsDistribution D ∧
                nuTwo G ≤ 4 * (∑ c, D c / Real.sqrt
                  (∑ d ∈ Finset.univ.filter (fun d => G d c), D d)) ^ 2 := by
            intro C hC G hG
            let c₀ : Fin C := ⟨0, hC⟩
            let f₀ : Fin C → ℝ := fun c => if c = c₀ then 1 else 0
            have hf₀ : ∀ c, 0 ≤ f₀ c := by intro c; simp [f₀]; split_ifs <;> norm_num
            have hsum₀ : (∑ c, f₀ c) = 1 := by simp [f₀]
            have hne : {x : ℝ | ∃ f : Fin C → ℝ, (∀ c, 0 ≤ f c) ∧ (∑ c, f c) = 1 ∧
                x = (∑ c, f c / Real.sqrt
                  (∑ d ∈ Finset.univ.filter (fun d => G d c), f d)) ^ 2}.Nonempty :=
              ⟨_, f₀, hf₀, hsum₀, rfl⟩
            have hν : 0 < nuTwo G := lt_of_lt_of_le zero_lt_one (hGraph C hC G hG).1
            obtain ⟨x, ⟨D, hD, hsum, hx⟩, hlt⟩ :=
              exists_lt_of_lt_csSup hne (show nuTwo G / 4 < nuTwo G by linarith)
            exact ⟨D, ⟨hD, hsum⟩, by rw [hx] at hlt; linarith⟩
          have hReduction :
              (∀ (K C : ℕ) [NeZero K], 2 ≤ K → 0 < C → ∀ G : Fin C → Fin C → Prop,
                (∀ d, G d d) → ∀ D : Fin C → ℝ, IsDistribution D →
                ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
                ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
                ∃ S : StochInstance K C, S.IsCoordinateIndependent ∧ S.D = D ∧
                  (1 / 128 : ℝ) * (∑ c, D c / Real.sqrt
                    (∑ d ∈ Finset.univ.filter (fun d => G d c), D d)) *
                    Real.sqrt ((K : ℝ) * T) ≤ stochRegret T (fun _ => G) S A) →
              ∃ c : ℝ, 0 < c ∧
                ∀ (K C : ℕ) [NeZero K], 2 ≤ K → 0 < C → ∀ G : Fin C → Fin C → Prop,
                (∀ d, G d d) → ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
                ∃ D : Fin C → ℝ, IsDistribution D ∧ ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
                  ∃ S : StochInstance K C, S.IsCoordinateIndependent ∧ S.D = D ∧
                    c * Real.sqrt (nuTwo G * K * T) ≤ stochRegret T (fun _ => G) S A := by
            intro hLower
            refine ⟨1 / 256, by norm_num, ?_⟩
            intro K C _ hK hC G hG
            obtain ⟨D, hD, hDν⟩ := hApprox C hC G hG
            obtain ⟨T₀, hT₀, hLower⟩ := hLower K C hK hC G hG D hD
            refine ⟨T₀, hT₀, ?_⟩
            intro T hT
            refine ⟨D, hD, ?_⟩
            intro A hA hAm
            obtain ⟨S, hSind, hSD, hS⟩ := hLower T hT A hA hAm
            refine ⟨S, hSind, hSD, le_trans ?_ hS⟩
            let W : ℝ := ∑ c, D c / Real.sqrt
              (∑ d ∈ Finset.univ.filter (fun d => G d c), D d)
            have hW : 0 ≤ W := Finset.sum_nonneg fun c _ =>
              div_nonneg (hD.1 c) (Real.sqrt_nonneg _)
            have hν : 0 ≤ nuTwo G := le_trans (by norm_num) (hGraph C hC G hG).1
            have hsqrt : Real.sqrt (nuTwo G) ≤ 2 * W := by
              apply (Real.sqrt_le_left (by positivity)).2
              nlinarith [hDν]
            rw [mul_assoc (nuTwo G), Real.sqrt_mul hν]
            change (1 / 256 : ℝ) * (Real.sqrt (nuTwo G) * Real.sqrt ((K : ℝ) * T)) ≤
              (1 / 128 : ℝ) * W * Real.sqrt ((K : ℝ) * T)
            nlinarith [mul_nonneg (sub_nonneg.2 hsqrt) (Real.sqrt_nonneg ((K : ℝ) * T))]
          have hBernoulli : ∀ (K C : ℕ) (D : Fin C → ℝ), IsDistribution D →
              ∀ (p : Fin K → Fin C → ℝ) (hp : ∀ i c, p i c ∈ Set.Icc (0 : ℝ) 1),
              ∃ S : StochInstance K C, S.IsCoordinateIndependent ∧ S.D = D ∧ S.mean = p ∧
                S.F = (fun i c => ProbabilityTheory.bernoulliMeasure 1 0 ⟨p i c, hp i c⟩) := by
            intro K C D hD p hp
            let F : Fin K → Fin C → MeasureTheory.Measure ℝ := fun i c =>
              ProbabilityTheory.bernoulliMeasure 1 0 ⟨p i c, hp i c⟩
            have hF : ∀ i c, MeasureTheory.IsProbabilityMeasure (F i c) := by
              intro i c
              dsimp [F]
              infer_instance
            letI : ∀ i c, MeasureTheory.IsProbabilityMeasure (F i c) := hF
            let S : StochInstance K C := {
              D := D
              F := F
              D_dist := hD
              F_prob := hF
              F_supp := by
                intro i c
                exact ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem _
                  measurableSet_Icc.compl (by simp) (by simp)
              roundLaw := fun _ => MeasureTheory.Measure.pi (fun i => MeasureTheory.Measure.pi (F i))
              round_prob := by intro t; infer_instance
              round_marginal := by
                intro t i c
                change MeasureTheory.Measure.map (Function.eval c ∘ Function.eval i)
                  (MeasureTheory.Measure.pi (fun i => MeasureTheory.Measure.pi (F i))) = F i c
                rw [← MeasureTheory.Measure.map_map (measurable_pi_apply c) (measurable_pi_apply i),
                  (MeasureTheory.measurePreserving_eval _ i).map_eq,
                  (MeasureTheory.measurePreserving_eval _ c).map_eq]
            }
            refine ⟨S, fun t => rfl, rfl, ?_, rfl⟩
            funext i c
            simp [StochInstance.mean, S, F, ProbabilityTheory.integral_bernoulliMeasure]
          have hSchedule : ∀ (K C : ℕ) (D : Fin C → ℝ), IsDistribution D →
              ∀ G : Fin C → Fin C → Prop,
              ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
              ∃ δ : Fin C → ℝ,
                (∀ c, 0 ≤ δ c ∧ δ c ≤ 1 / 4) ∧
                (∀ c, δ c ^ 2 * T *
                  (∑ d ∈ Finset.univ.filter (fun d => G d c), D d) ≤ (K : ℝ) / 256) ∧
                (T : ℝ) / 8 * (∑ c, D c * δ c) =
                  (1 / 128 : ℝ) * (∑ c, D c / Real.sqrt
                    (∑ d ∈ Finset.univ.filter (fun d => G d c), D d)) *
                    Real.sqrt ((K : ℝ) * T) := by
            intro K C D hD G
            let Q : Fin C → ℝ := fun c => ∑ d ∈ Finset.univ.filter (fun d => G d c), D d
            have hQ : ∀ c, 0 ≤ Q c := fun c => Finset.sum_nonneg (fun d _ => hD.1 d)
            obtain ⟨N, hN⟩ := exists_nat_gt (∑ c, (K : ℝ) / Q c)
            refine ⟨N + 1, Nat.succ_pos N, ?_⟩
            intro T hT
            have hTpos : 0 < T := lt_of_lt_of_le (Nat.succ_pos N) hT
            have hTposR : 0 < (T : ℝ) := Nat.cast_pos.2 hTpos
            have hsT : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTposR
            have hsum : (∑ c, (K : ℝ) / Q c) ≤ T := by
              have hNT : (N : ℝ) < T := by exact_mod_cast (show N < T by omega)
              linarith
            let a : ℝ := Real.sqrt (K : ℝ) / (16 * Real.sqrt (T : ℝ))
            let δ : Fin C → ℝ := fun c => a / Real.sqrt (Q c)
            have ha : 0 ≤ a := by dsimp [a]; positivity
            have hδ : ∀ c, 0 ≤ δ c ∧ δ c ≤ 1 / 4 := by
              intro c
              refine ⟨div_nonneg ha (Real.sqrt_nonneg _), ?_⟩
              by_cases hQc : Q c = 0
              · simp [δ, hQc]
              have hQcpos : 0 < Q c := lt_of_le_of_ne (hQ c) (Ne.symm hQc)
              have hsQ : 0 < Real.sqrt (Q c) := Real.sqrt_pos.2 hQcpos
              have hdiv : (K : ℝ) / Q c ≤ T := le_trans
                (Finset.single_le_sum (fun b _ => div_nonneg (Nat.cast_nonneg K) (hQ b))
                  (Finset.mem_univ c)) hsum
              have hKT : (K : ℝ) ≤ (T : ℝ) * Q c := (div_le_iff₀ hQcpos).1 hdiv
              have hsKT := Real.sqrt_le_sqrt hKT
              rw [Real.sqrt_mul (le_of_lt hTposR)] at hsKT
              dsimp [δ, a]
              rw [div_le_iff₀ hsQ, div_le_iff₀ (by positivity : 0 < 16 * Real.sqrt (T : ℝ))]
              nlinarith [mul_nonneg (Real.sqrt_nonneg (T : ℝ)) (Real.sqrt_nonneg (Q c))]
            refine ⟨δ, hδ, ?_, ?_⟩
            · intro c
              change (δ c) ^ 2 * (T : ℝ) * Q c ≤ (K : ℝ) / 256
              by_cases hQc : Q c = 0
              · simp only [hQc, mul_zero]
                positivity
              have hsQ : Real.sqrt (Q c) ≠ 0 := (Real.sqrt_ne_zero (hQ c)).2 hQc
              have hsTe : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt hsT
              have heq : (δ c) ^ 2 * (T : ℝ) * Q c = (K : ℝ) / 256 := by
                dsimp [δ, a]
                rw [div_pow, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg K),
                  Real.sq_sqrt (le_of_lt hTposR), Real.sq_sqrt (hQ c)]
                field_simp
                <;> ring
              exact heq.le
            · have hsumδ : (∑ c, D c * δ c) = a * ∑ c, D c / Real.sqrt (Q c) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro c hc
                dsimp [δ]
                ring
              rw [hsumδ]
              change (T : ℝ) / 8 * (a * ∑ c, D c / Real.sqrt (Q c)) =
                (1 / 128 : ℝ) * (∑ c, D c / Real.sqrt (Q c)) * Real.sqrt ((K : ℝ) * T)
              rw [Real.sqrt_mul (Nat.cast_nonneg K)]
              dsimp [a]
              calc
                _ = (1 / 128 : ℝ) * (∑ c, D c / Real.sqrt (Q c)) *
                    (Real.sqrt (K : ℝ) * ((T : ℝ) / Real.sqrt (T : ℝ))) := by ring
                _ = _ := by rw [Real.div_sqrt]
          have hHardReduction :
              (∀ (K C : ℕ) [NeZero K], 2 ≤ K → ∀ (D : Fin C → ℝ), IsDistribution D →
                ∀ (G : Fin C → Fin C → Prop), (∀ d, G d d) → ∀ (T : ℕ) (δ : Fin C → ℝ),
                (∀ c, 0 ≤ δ c ∧ δ c ≤ 1 / 4) →
                (∀ c, δ c ^ 2 * T *
                  (∑ d ∈ Finset.univ.filter (fun d => G d c), D d) ≤ (K : ℝ) / 256) →
                ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
                ∃ S : StochInstance K C, S.IsCoordinateIndependent ∧ S.D = D ∧
                  (T : ℝ) / 8 * (∑ c, D c * δ c) ≤ stochRegret T (fun _ => G) S A) →
              ∃ c : ℝ, 0 < c ∧
                ∀ (K C : ℕ) [NeZero K], 2 ≤ K → 0 < C → ∀ G : Fin C → Fin C → Prop,
                (∀ d, G d d) → ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
                ∃ D : Fin C → ℝ, IsDistribution D ∧ ∀ A : Policy K C, A.IsValid → A.IsMeasurable →
                  ∃ S : StochInstance K C, S.IsCoordinateIndependent ∧ S.D = D ∧
                    c * Real.sqrt (nuTwo G * K * T) ≤ stochRegret T (fun _ => G) S A := by
            intro hHard
            apply hReduction
            intro K C _ hK hC G hG D hD
            obtain ⟨T₀, hT₀, hSched⟩ := hSchedule K C D hD G
            refine ⟨T₀, hT₀, ?_⟩
            intro T hT A hA hAm
            obtain ⟨δ, hδ, hsmall, heq⟩ := hSched T hT
            obtain ⟨S, hind, hSD, hS⟩ := hHard K C hK D hD G hG T δ hδ hsmall A hA hAm
            exact ⟨S, hind, hSD, heq ▸ hS⟩
          have hLogHellinger : ∀ x y : ℝ, 0 < x → 0 < y →
              (Real.sqrt x - Real.sqrt y) ^ 2 ≤ x * Real.log (x / y) + y - x := by
            intro x y hx hy
            have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
            have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
            have hlog := Real.log_le_sub_one_of_pos (div_pos hsy hsx)
            rw [Real.log_div (ne_of_gt hsy) (ne_of_gt hsx),
              Real.log_sqrt hy.le, Real.log_sqrt hx.le] at hlog
            have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * x by positivity)
            have hcross : x * (Real.sqrt y / Real.sqrt x) = Real.sqrt x * Real.sqrt y := by
              calc
                _ = (Real.sqrt x * Real.sqrt x) * (Real.sqrt y / Real.sqrt x) := by
                  rw [Real.mul_self_sqrt hx.le]
                _ = _ := by field_simp <;> ring
            rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
            nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
          have hPinsker : ∀ (Ω : Type) [Fintype Ω] (P Q : Ω → ℝ),
              (∀ ω, 0 ≤ P ω) → (∀ ω, 0 ≤ Q ω) →
              (∑ ω, P ω) = 1 → (∑ ω, Q ω) = 1 →
              (∀ ω, P ω = 0 ↔ Q ω = 0) → ∀ X : Ω → ℝ,
              (∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) →
              0 ≤ (∑ ω, P ω * Real.log (P ω / Q ω)) ∧
              |(∑ ω, P ω * X ω) - ∑ ω, Q ω * X ω| ≤
                2 * Real.sqrt (∑ ω, P ω * Real.log (P ω / Q ω)) := by
            intro Ω _ P Q hP hQ hPsum hQsum hsupp X hX
            let H : ℝ := ∑ ω, (Real.sqrt (P ω) - Real.sqrt (Q ω)) ^ 2
            let B : ℝ := ∑ ω, (Real.sqrt (P ω) + Real.sqrt (Q ω)) ^ 2
            let L : ℝ := ∑ ω, |Real.sqrt (P ω) - Real.sqrt (Q ω)| *
              (Real.sqrt (P ω) + Real.sqrt (Q ω))
            let J : ℝ := ∑ ω, P ω * Real.log (P ω / Q ω)
            have hHJ : H ≤ J := by
              have hpoint : ∀ ω, (Real.sqrt (P ω) - Real.sqrt (Q ω)) ^ 2 ≤
                  P ω * Real.log (P ω / Q ω) + Q ω - P ω := by
                intro ω
                by_cases hzero : P ω = 0
                · simp [hzero, (hsupp ω).1 hzero]
                · exact hLogHellinger _ _
                    (lt_of_le_of_ne (hP ω) (Ne.symm hzero))
                    (lt_of_le_of_ne (hQ ω) (Ne.symm (mt (hsupp ω).2 hzero)))
              have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hpoint ω)
              simpa [H, J, Finset.sum_add_distrib, Finset.sum_sub_distrib, hQsum, hPsum] using hsum
            have hH : 0 ≤ H := Finset.sum_nonneg fun ω _ => sq_nonneg _
            have hJ : 0 ≤ J := le_trans hH hHJ
            have hB : B ≤ 4 := by
              have hpoint : ∀ ω, (Real.sqrt (P ω) + Real.sqrt (Q ω)) ^ 2 ≤ 2 * P ω + 2 * Q ω := by
                intro ω
                nlinarith [sq_nonneg (Real.sqrt (P ω) - Real.sqrt (Q ω)),
                  Real.sq_sqrt (hP ω), Real.sq_sqrt (hQ ω)]
              have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hpoint ω)
              change (∑ ω, (Real.sqrt (P ω) + Real.sqrt (Q ω)) ^ 2) ≤ 4
              calc
                _ ≤ ∑ ω, (2 * P ω + 2 * Q ω) := hsum
                _ = 4 := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
                  hPsum, hQsum]; norm_num
            have hL : 0 ≤ L := Finset.sum_nonneg fun ω _ =>
              mul_nonneg (abs_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            have hCS : L ^ 2 ≤ H * B := by
              simpa [L, H, B, sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
                (fun ω => |Real.sqrt (P ω) - Real.sqrt (Q ω)|)
                (fun ω => Real.sqrt (P ω) + Real.sqrt (Q ω))
            have hLbound : L ≤ 2 * Real.sqrt J := by
              have hHB : H * B ≤ 4 * H := by nlinarith
              nlinarith [Real.sq_sqrt hJ, Real.sqrt_nonneg J]
            have hAbs : |(∑ ω, P ω * X ω) - ∑ ω, Q ω * X ω| ≤ L := by
              rw [← Finset.sum_sub_distrib]
              calc
                _ ≤ ∑ ω, |P ω * X ω - Q ω * X ω| := Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ ω, |P ω - Q ω| := by
                  apply Finset.sum_le_sum
                  intro ω hω
                  rw [← sub_mul, abs_mul, abs_of_nonneg (hX ω).1]
                  exact mul_le_of_le_one_right (abs_nonneg _) (hX ω).2
                _ = L := by
                  apply Finset.sum_congr rfl
                  intro ω hω
                  have heq : P ω - Q ω = (Real.sqrt (P ω) - Real.sqrt (Q ω)) *
                      (Real.sqrt (P ω) + Real.sqrt (Q ω)) := by
                    nlinarith [Real.sq_sqrt (hP ω), Real.sq_sqrt (hQ ω)]
                  rw [heq, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
            exact ⟨hJ, le_trans hAbs hLbound⟩
          have hMultiTest : ∀ (K : ℕ) [NeZero K], 2 ≤ K →
              ∀ (Ω : Type) [Fintype Ω] (P : Ω → ℝ) (R : Fin K → Ω → ℝ),
              (∀ ω, 0 ≤ P ω) → (∀ i ω, 0 ≤ R i ω) →
              (∑ ω, P ω) = 1 → (∀ i, ∑ ω, R i ω = 1) →
              (∀ i ω, P ω = 0 ↔ R i ω = 0) →
              ∀ X : Fin K → Ω → ℝ, (∀ i ω, 0 ≤ X i ω) → (∀ ω, ∑ i, X i ω = 1) →
              (∑ i, ∑ ω, P ω * Real.log (P ω / R i ω)) ≤ (K : ℝ) / 64 →
              (∑ i, ∑ ω, R i ω * X i ω) ≤ 3 * (K : ℝ) / 4 := by
            intro K _ hK Ω _ P R hP hR hPsum hRsum hsupp X hX hXsum hInfo
            let J : Fin K → ℝ := fun i => ∑ ω, P ω * Real.log (P ω / R i ω)
            have hXi : ∀ i ω, X i ω ≤ 1 := by
              intro i ω
              rw [← hXsum ω]
              exact Finset.single_le_sum (fun j _ => hX j ω) (Finset.mem_univ i)
            have hBound : ∀ i, 0 ≤ J i ∧
                (∑ ω, R i ω * X i ω) ≤ (∑ ω, P ω * X i ω) + 2 * Real.sqrt (J i) := by
              intro i
              have hp := hPinsker Ω P (R i) hP (hR i) hPsum (hRsum i) (hsupp i) (X i)
                (fun ω => ⟨hX i ω, hXi i ω⟩)
              refine ⟨hp.1, ?_⟩
              have hn := neg_le_abs ((∑ ω, P ω * X i ω) - ∑ ω, R i ω * X i ω)
              change _ ≤ _ + 2 * Real.sqrt (J i)
              linarith [hp.2]
            have hCS : (∑ i, Real.sqrt (J i)) ^ 2 ≤ (K : ℝ) * ∑ i, J i := by
              have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
                (fun i : Fin K => Real.sqrt (J i)) (fun _ : Fin K => (1 : ℝ))
              simpa [Real.sq_sqrt, fun i => (hBound i).1, mul_comm] using h
            have hKnonneg : (0 : ℝ) ≤ K := Nat.cast_nonneg K
            have hcs : (∑ i, Real.sqrt (J i)) ≤ (K : ℝ) / 8 := by
              have hI : (K : ℝ) * (∑ i, J i) ≤ (K : ℝ) * ((K : ℝ) / 64) :=
                mul_le_mul_of_nonneg_left hInfo hKnonneg
              have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => Real.sqrt_nonneg (J i))
              nlinarith
            have hbaseline : (∑ i, ∑ ω, P ω * X i ω) = 1 := by
              rw [Finset.sum_comm]
              simp_rw [← Finset.mul_sum, hXsum, mul_one]
              exact hPsum
            have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hBound i).2)
            rw [Finset.sum_add_distrib, hbaseline, ← Finset.mul_sum] at hsum
            have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
            linarith
          have hCausalStep : ∀ (Ω : Type) [Fintype Ω]
              (Q : (t : ℕ) → (Fin t → Ω) → Ω → ℝ) (T : ℕ) (h : Fin T → Ω) (a : Ω),
              (∏ t : Fin (T + 1), Q t
                (fun s => Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a (Fin.castLE t.2.le s))
                (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a t)) =
              (∏ t : Fin T, Q t (fun s => h (Fin.castLE t.2.le s)) (h t)) * Q T h a := by
            intro Ω _ Q T h a
            rw [Fin.prod_univ_castSucc]
            congr 1
            · apply Finset.prod_congr rfl
              intro t ht
              have hpref : (fun s : Fin (t : ℕ) =>
                  Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a (Fin.castLE t.castSucc.2.le s)) =
                  (fun s => h (Fin.castLE t.2.le s)) := by
                funext s
                change Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a
                  (Fin.castSucc (Fin.castLE t.2.le s)) = _
                exact Fin.snoc_castSucc (α := fun _ : Fin (T + 1) => Ω) a h _
              exact congrArg₂ (Q (t : ℕ)) hpref (by simp)
            · have hpref : (fun s : Fin T =>
                  Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a (Fin.castLE (Fin.last T).2.le s)) = h := by
                funext s
                change Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a s.castSucc = h s
                exact Fin.snoc_castSucc (α := fun _ : Fin (T + 1) => Ω) a h s
              exact congrArg₂ (Q T) hpref (by simp)
          have hCausalSum : ∀ (Ω : Type) [Fintype Ω]
              (Q : (t : ℕ) → (Fin t → Ω) → Ω → ℝ),
              (∀ t h, ∑ a, Q t h a = 1) → ∀ T : ℕ,
              ∑ τ : Fin T → Ω, ∏ t : Fin T,
                Q t (fun s => τ (Fin.castLE t.2.le s)) (τ t) = 1 := by
            intro Ω _ Q hQ T
            induction T with
            | zero => simp
            | succ T ih =>
              let P : (n : ℕ) → (Fin n → Ω) → ℝ := fun n τ =>
                ∏ t : Fin n, Q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)
              have hstep : ∀ (h : Fin T → Ω) (a : Ω),
                  P (T + 1) (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a) = P T h * Q T h a :=
                hCausalStep Ω Q T
              change (∑ τ : Fin (T + 1) → Ω, P (T + 1) τ) = 1
              calc
                _ = ∑ z : Ω × (Fin T → Ω), P (T + 1) (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) z.2 z.1) := by
                  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T + 1) => Ω))
                    (fun z => P (T + 1) (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) z.2 z.1)) (P (T + 1)) (fun _ => rfl)).symm
                _ = ∑ h : Fin T → Ω, ∑ a : Ω, P T h * Q T h a := by
                  rw [Fintype.sum_prod_type, Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro h hh
                  apply Finset.sum_congr rfl
                  intro a ha
                  exact hstep h a
                _ = ∑ h : Fin T → Ω, P T h := by
                  apply Finset.sum_congr rfl
                  intro h hh
                  rw [← Finset.mul_sum, hQ, mul_one]
                _ = 1 := ih
          have hCausalCostStep : ∀ (Ω : Type) [Fintype Ω]
              (Q : (t : ℕ) → (Fin t → Ω) → Ω → ℝ) (T : ℕ) (h : Fin T → Ω) (a : Ω),
              (∑ t : Fin (T + 1), Q t
                (fun s => Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a (Fin.castLE t.2.le s))
                (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a t)) =
              (∑ t : Fin T, Q t (fun s => h (Fin.castLE t.2.le s)) (h t)) + Q T h a := by
            intro Ω _ Q T h a
            rw [Fin.sum_univ_castSucc]
            congr 1
            · apply Finset.sum_congr rfl
              intro t ht
              have hpref : (fun s : Fin (t : ℕ) =>
                  Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a (Fin.castLE t.castSucc.2.le s)) =
                  (fun s => h (Fin.castLE t.2.le s)) := by
                funext s
                change Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a
                  (Fin.castSucc (Fin.castLE t.2.le s)) = _
                exact Fin.snoc_castSucc (α := fun _ : Fin (T + 1) => Ω) a h _
              exact congrArg₂ (Q (t : ℕ)) hpref (by simp)
            · have hpref : (fun s : Fin T =>
                  Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a (Fin.castLE (Fin.last T).2.le s)) = h := by
                funext s
                change Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a s.castSucc = h s
                exact Fin.snoc_castSucc (α := fun _ : Fin (T + 1) => Ω) a h s
              exact congrArg₂ (Q T) hpref (by simp)
          have hMartingale : ∀ (Ω : Type) [Fintype Ω]
              (Q Y : (t : ℕ) → (Fin t → Ω) → Ω → ℝ),
              (∀ t h, ∑ a, Q t h a = 1) →
              (∀ t h, ∑ a, Q t h a * Y t h a = 0) → ∀ T : ℕ,
              (∑ τ : Fin T → Ω,
                (∏ t : Fin T, Q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) *
                (∑ t : Fin T, Y t (fun s => τ (Fin.castLE t.2.le s)) (τ t))) = 0 := by
            intro Ω _ Q Y hQ hY T
            let P : (n : ℕ) → (Fin n → Ω) → ℝ := fun n τ =>
              ∏ t : Fin n, Q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)
            let V : (n : ℕ) → (Fin n → Ω) → ℝ := fun n τ =>
              ∑ t : Fin n, Y t (fun s => τ (Fin.castLE t.2.le s)) (τ t)
            change (∑ τ, P T τ * V T τ) = 0
            induction T with
            | zero => simp [V]
            | succ T ih =>
              have hp (h : Fin T → Ω) (a : Ω) :
                  P (T + 1) (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a) =
                  P T h * Q T h a := hCausalStep Ω Q T h a
              have hv (h : Fin T → Ω) (a : Ω) :
                  V (T + 1) (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) h a) =
                  V T h + Y T h a := hCausalCostStep Ω Y T h a
              calc
                _ = ∑ z : Ω × (Fin T → Ω),
                    P (T + 1) (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) z.2 z.1) *
                      V (T + 1) (Fin.snoc (α := fun _ : Fin (T + 1) => Ω) z.2 z.1) :=
                  (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T + 1) => Ω)) _ _ (fun _ => rfl)).symm
                _ = ∑ h : Fin T → Ω, ∑ a : Ω, P T h * Q T h a * (V T h + Y T h a) := by
                  rw [Fintype.sum_prod_type, Finset.sum_comm]
                  simp_rw [hp, hv]
                _ = ∑ h : Fin T → Ω, P T h * V T h := by
                  apply Finset.sum_congr rfl
                  intro h hh
                  have heq : ∀ a, P T h * Q T h a * (V T h + Y T h a) =
                      (P T h * V T h) * Q T h a + P T h * (Q T h a * Y T h a) := by
                    intro a
                    ring
                  simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum, hQ, hY,
                    mul_one, mul_zero, add_zero]
                _ = 0 := ih
          have hScalarKL : ∀ x y u v : ℝ, (x = 0 ↔ y = 0) → (u = 0 ↔ v = 0) →
              (x * u) * Real.log ((x * u) / (y * v)) =
                u * (x * Real.log (x / y)) + x * (u * Real.log (u / v)) := by
            intro x y u v hxy huv
            by_cases hx : x = 0
            · simp [hx, hxy.1 hx]
            by_cases hu : u = 0
            · simp [hu, huv.1 hu]
            have hy : y ≠ 0 := mt hxy.2 hx
            have hv : v ≠ 0 := mt huv.2 hu
            rw [← div_mul_div_comm, Real.log_mul (div_ne_zero hx hy) (div_ne_zero hu hv)]
            ring
          have hCausalKL : ∀ (Ω : Type) [Fintype Ω]
              (Q R : (t : ℕ) → (Fin t → Ω) → Ω → ℝ),
              (∀ t h, ∑ a, Q t h a = 1) → (∀ t h, ∑ a, R t h a = 1) →
              (∀ t h a, Q t h a = 0 ↔ R t h a = 0) → ∀ T : ℕ,
              (∑ τ : Fin T → Ω,
                (∏ t : Fin T, Q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) *
                Real.log ((∏ t : Fin T, Q t (fun s => τ (Fin.castLE t.2.le s)) (τ t)) /
                  (∏ t : Fin T, R t (fun s => τ (Fin.castLE t.2.le s)) (τ t)))) =
              ∑ t : Fin T, ∑ h : Fin (t : ℕ) → Ω,
                (∏ s : Fin (t : ℕ), Q s (fun u => h (Fin.castLE s.2.le u)) (h s)) *
                  (∑ a, Q t h a * Real.log (Q t h a / R t h a)) := by
            intro Ω _ Q R hQ hR hsupp T
            let P : ((t : ℕ) → (Fin t → Ω) → Ω → ℝ) → (n : ℕ) → (Fin n → Ω) → ℝ :=
              fun F n τ => ∏ t : Fin n, F t (fun s => τ (Fin.castLE t.2.le s)) (τ t)
            let J : ℕ → ℝ := fun n => ∑ τ : Fin n → Ω,
              P Q n τ * Real.log (P Q n τ / P R n τ)
            let B : ℕ → ℝ := fun n => ∑ h : Fin n → Ω,
              P Q n h * (∑ a, Q n h a * Real.log (Q n h a / R n h a))
            have hPsupp : ∀ n (h : Fin n → Ω), P Q n h = 0 ↔ P R n h = 0 := by
              intro n h
              simp only [P, Finset.prod_eq_zero_iff]
              constructor
              · rintro ⟨t, ht, hz⟩
                exact ⟨t, ht, (hsupp _ _ _).1 hz⟩
              · rintro ⟨t, ht, hz⟩
                exact ⟨t, ht, (hsupp _ _ _).2 hz⟩
            have hJstep : ∀ n, J (n + 1) = J n + B n := by
              intro n
              have hpQ (h : Fin n → Ω) (a : Ω) :
                  P Q (n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Ω) h a) =
                  P Q n h * Q n h a := hCausalStep Ω Q n h a
              have hpR (h : Fin n → Ω) (a : Ω) :
                  P R (n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Ω) h a) =
                  P R n h * R n h a := hCausalStep Ω R n h a
              change (∑ τ : Fin (n + 1) → Ω,
                P Q (n + 1) τ * Real.log (P Q (n + 1) τ / P R (n + 1) τ)) = _
              calc
                _ = ∑ z : Ω × (Fin n → Ω),
                    P Q (n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Ω) z.2 z.1) *
                    Real.log (P Q (n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Ω) z.2 z.1) /
                      P R (n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => Ω) z.2 z.1)) := by
                  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => Ω))
                    _ _ (fun _ => rfl)).symm
                _ = ∑ h : Fin n → Ω, ∑ a : Ω,
                    (Q n h a * (P Q n h * Real.log (P Q n h / P R n h)) +
                      P Q n h * (Q n h a * Real.log (Q n h a / R n h a))) := by
                  rw [Fintype.sum_prod_type, Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro h hh
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [hpQ, hpR]
                  exact hScalarKL _ _ _ _ (hPsupp n h) (hsupp n h a)
                _ = ∑ h : Fin n → Ω,
                    ((∑ a, Q n h a) * (P Q n h * Real.log (P Q n h / P R n h)) +
                      P Q n h * (∑ a, Q n h a * Real.log (Q n h a / R n h a))) := by
                  apply Finset.sum_congr rfl
                  intro h hh
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
                _ = J n + B n := by
                  simp_rw [hQ, one_mul]
                  rw [Finset.sum_add_distrib]
            have hJ : ∀ n, J n = ∑ t : Fin n, B t := by
              intro n
              induction n with
              | zero => simp [J, P]
              | succ n ih =>
                rw [hJstep, Fin.sum_univ_castSucc, ih]
                rfl
            exact hJ T
          have hIndependentKL : ∀ (Ω : Type) [Fintype Ω] (p q : ℕ → Ω → ℝ),
              (∀ t, ∑ a, p t a = 1) → (∀ t, ∑ a, q t a = 1) →
              (∀ t a, p t a = 0 ↔ q t a = 0) → ∀ T : ℕ,
              (∑ τ : Fin T → Ω, (∏ t : Fin T, p t (τ t)) *
                Real.log ((∏ t : Fin T, p t (τ t)) / (∏ t : Fin T, q t (τ t)))) =
              ∑ t : Fin T, ∑ a, p t a * Real.log (p t a / q t a) := by
            intro Ω _ p q hp hq hsupp T
            have h := hCausalKL Ω (fun t _ => p t) (fun t _ => q t)
              (fun t _ => hp t) (fun t _ => hq t) (fun t _ a => hsupp t a) T
            rw [h]
            apply Finset.sum_congr rfl
            intro t ht
            rw [← Finset.sum_mul]
            have hn := hCausalSum Ω (fun t _ => p t) (fun t _ => hp t) (t : ℕ)
            rw [hn, one_mul]
          have hProductKL : ∀ (n : ℕ) (f g : Fin n → Bool → ℝ),
              (∀ i, ∑ v, f i v = 1) → (∀ i, ∑ v, g i v = 1) →
              (∀ i v, f i v = 0 ↔ g i v = 0) →
              (∑ b : Fin n → Bool, (∏ i, f i (b i)) *
                Real.log ((∏ i, f i (b i)) / (∏ i, g i (b i)))) =
              ∑ i, ∑ v, f i v * Real.log (f i v / g i v) := by
            intro n f g hf hg hsupp
            let f' : ℕ → Bool → ℝ := fun t v => if ht : t < n then f ⟨t, ht⟩ v else if v then 1 else 0
            let g' : ℕ → Bool → ℝ := fun t v => if ht : t < n then g ⟨t, ht⟩ v else if v then 1 else 0
            have hf' : ∀ t, ∑ v, f' t v = 1 := by
              intro t
              dsimp [f']
              split_ifs with ht
              · exact hf ⟨t, ht⟩
              · simp [Fintype.sum_bool]
            have hg' : ∀ t, ∑ v, g' t v = 1 := by
              intro t
              dsimp [g']
              split_ifs with ht
              · exact hg ⟨t, ht⟩
              · simp [Fintype.sum_bool]
            have hs' : ∀ t v, f' t v = 0 ↔ g' t v = 0 := by
              intro t v
              dsimp [f', g']
              by_cases ht : t < n
              · simp only [dif_pos ht]
                exact hsupp ⟨t, ht⟩ v
              · simp only [dif_neg ht]
            have h := hIndependentKL Bool f' g' hf' hg' hs' n
            have hfeq : ∀ (t : Fin n) v, f' t v = f t v := by intro t v; simp [f', t.2]
            have hgeq : ∀ (t : Fin n) v, g' t v = g t v := by intro t v; simp [g', t.2]
            simpa only [hfeq, hgeq] using h
          have hCoinKL : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
              (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (1 / 2 + δ)) +
                (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (1 / 2 - δ)) ≤ 4 * δ ^ 2 := by
            intro δ hδ hδu
            have hs : δ ^ 2 ≤ 1 / 16 := by
              nlinarith [mul_self_le_mul_self hδ hδu]
            have hp : 0 < (1 / 2 : ℝ) + δ := by linarith
            have hm : 0 < (1 / 2 : ℝ) - δ := by linarith
            have hz : 0 < 1 - 4 * δ ^ 2 := by linarith
            have hzhalf : (1 / 2 : ℝ) ≤ 1 - 4 * δ ^ 2 := by linarith
            have hpm : ((1 / 2 : ℝ) + δ) * (1 / 2 - δ) = (1 - 4 * δ ^ 2) / 4 := by ring
            calc
              _ = (1 / 2 : ℝ) * Real.log
                  (((1 / 2 : ℝ) / (1 / 2 + δ)) * ((1 / 2 : ℝ) / (1 / 2 - δ))) := by
                rw [Real.log_mul (ne_of_gt (div_pos (by norm_num) hp))
                  (ne_of_gt (div_pos (by norm_num) hm))]
                ring
              _ = (1 / 2 : ℝ) * Real.log (1 / (1 - 4 * δ ^ 2)) := by
                congr 2
                rw [div_mul_div_comm, hpm]
                field_simp
                <;> ring
              _ ≤ (1 / 2 : ℝ) * (1 / (1 - 4 * δ ^ 2) - 1) :=
                mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos zero_lt_one hz))
                  (by norm_num)
              _ = 2 * δ ^ 2 / (1 - 4 * δ ^ 2) := by field_simp; ring
              _ ≤ 2 * δ ^ 2 / (1 / 2 : ℝ) := by gcongr
              _ = 4 * δ ^ 2 := by ring
          have hAlgMeasurable : ∀ (K C T : ℕ)
              (G : Fin K → Fin C → Fin C → Prop) (D : Fin C → ℝ) (A : Policy K C),
              A.IsMeasurable → Measurable (fun r : Fin T → Fin K → Fin C → ℝ => algReward G D A r) := by
            intro K C T G D A hAm
            have hfeedback : ∀ (t : Fin T) (c : Fin C) (i : Fin K),
                Measurable (fun r : Fin T → Fin K → Fin C → ℝ => feedback G r t c i) := by
              intro t c i
              apply measurable_pi_lambda
              intro c'
              dsimp [feedback]
              split_ifs <;> fun_prop
            have hhist : ∀ (τ : Fin T → Fin C × Fin K) (t : Fin T),
                Measurable (fun r : Fin T → Fin K → Fin C → ℝ => hist G r τ t) := by
              intro τ t
              apply measurable_pi_lambda
              intro s
              dsimp [hist]
              exact measurable_const.prodMk (measurable_const.prodMk (hfeedback _ _ _))
            have hAction : ∀ (τ : Fin T → Fin C × Fin K) (t : Fin T),
                Measurable (fun r : Fin T → Fin K → Fin C → ℝ =>
                  A t (hist G r τ t) (τ t).1 (τ t).2) := by
              intro τ t
              exact (hAm t (τ t).1 (τ t).2).comp (hhist τ t)
            unfold algReward expect trajProb
            apply Finset.measurable_sum
            intro τ hτ
            apply Measurable.mul
            · apply Finset.measurable_prod
              intro t ht
              exact measurable_const.mul (hAction τ t)
            · apply Finset.measurable_sum
              intro t ht
              fun_prop
          apply hHardReduction
          intro K C _ hK D hD G hG T δ hδ hsmall A hA hAm
          unfold Policy at A
          let p : (Fin C → Fin K) → Fin K → Fin C → ℝ :=
            fun b i c => 1 / 2 + if i = b c then δ c else 0
          have hp : ∀ b i c, p b i c ∈ Set.Icc (0 : ℝ) 1 := by
            intro b i c
            dsimp [p]
            split_ifs <;> constructor <;> linarith [(hδ c).1, (hδ c).2]
          choose S hind hSD hmean hF using fun b => hBernoulli K C D hD (p b) (hp b)
          let Ω := Fin C × Fin K × (Fin C → Bool)
          let decode : (t : ℕ) → (Fin t → Ω) → Fin t → Obs K C :=
            fun t h s => ((h s).1, (h s).2.1, fun c => if (h s).2.2 c then 1 else 0)
          let coin : ℝ → Bool → ℝ := fun u v => if v then u else 1 - u
          let bit : (Fin K → Fin C → ℝ) → Fin C → Fin K → Fin C → Bool → ℝ :=
            fun m c i d v => if G c d then coin (m i d) v else if v then 0 else 1
          let Q : (Fin K → Fin C → ℝ) → (t : ℕ) → (Fin t → Ω) → Ω → ℝ :=
            fun m t h o => D o.1 * A t (decode t h) o.1 o.2.1 *
              ∏ d, bit m o.1 o.2.1 d (o.2.2 d)
          have hBitsSum : ∀ (m : Fin K → Fin C → ℝ) (c : Fin C) (i : Fin K),
              (∑ b : Fin C → Bool, ∏ d, bit m c i d (b d)) = 1 := by
            intro m c i
            rw [← Fintype.prod_sum]
            apply Finset.prod_eq_one
            intro d hd
            dsimp [bit]
            split_ifs <;> simp [coin, Fintype.sum_bool] <;> ring
          have hQsum : ∀ (m : Fin K → Fin C → ℝ) t h, ∑ o, Q m t h o = 1 := by
            intro m t h
            change (∑ o : Fin C × (Fin K × (Fin C → Bool)),
              D o.1 * A t (decode t h) o.1 o.2.1 *
                ∏ d, bit m o.1 o.2.1 d (o.2.2 d)) = 1
            simp_rw [Fintype.sum_prod_type]
            simp_rw [← Finset.mul_sum, hBitsSum, mul_one]
            simp_rw [← Finset.mul_sum, hA.2, mul_one]
            exact hD.2
          have hQnonneg : ∀ (m : Fin K → Fin C → ℝ),
              (∀ i c, m i c ∈ Set.Icc (0 : ℝ) 1) → ∀ t h o, 0 ≤ Q m t h o := by
            intro m hm t h o
            dsimp [Q]
            apply mul_nonneg (mul_nonneg (hD.1 _) (hA.1 _ _ _ _))
            apply Finset.prod_nonneg
            intro d hd
            dsimp [bit, coin]
            split_ifs <;> first | positivity | linarith [(hm o.2.1 d).1, (hm o.2.1 d).2]
          have hcoinPos : ∀ u : ℝ, 0 < u → u < 1 → ∀ v, 0 < coin u v := by
            intro u hu hu1 v
            cases v <;> dsimp [coin] <;> linarith
          have hbitNorm : ∀ (m : Fin K → Fin C → ℝ) c i d, ∑ v, bit m c i d v = 1 := by
            intro m c i d
            dsimp [bit]
            split_ifs <;> simp [coin, Fintype.sum_bool] <;> ring
          have hBitsSupport : ∀ (m r : Fin K → Fin C → ℝ),
              (∀ i c, 0 < m i c ∧ m i c < 1) → (∀ i c, 0 < r i c ∧ r i c < 1) →
              ∀ (c : Fin C) (i : Fin K) (b : Fin C → Bool), (∏ d, bit m c i d (b d)) = 0 ↔ (∏ d, bit r c i d (b d)) = 0 := by
            intro m r hm hr c i b
            have hbit : ∀ d, bit m c i d (b d) = 0 ↔ bit r c i d (b d) = 0 := by
              intro d
              by_cases hg : G c d
              · simp [bit, hg, ne_of_gt (hcoinPos _ (hm i d).1 (hm i d).2 (b d)),
                  ne_of_gt (hcoinPos _ (hr i d).1 (hr i d).2 (b d))]
              · simp only [bit, if_neg hg]
            simp only [Finset.prod_eq_zero_iff]
            constructor
            · rintro ⟨d, hd, hz⟩
              exact ⟨d, hd, (hbit d).1 hz⟩
            · rintro ⟨d, hd, hz⟩
              exact ⟨d, hd, (hbit d).2 hz⟩
          have hQSupport : ∀ (m r : Fin K → Fin C → ℝ),
              (∀ i c, 0 < m i c ∧ m i c < 1) → (∀ i c, 0 < r i c ∧ r i c < 1) →
              ∀ t h o, Q m t h o = 0 ↔ Q r t h o = 0 := by
            intro m r hm hr t h o
            dsimp [Q]
            simp only [mul_eq_zero, hBitsSupport m r hm hr]
          let P : (Fin K → Fin C → ℝ) → (n : ℕ) → (Fin n → Ω) → ℝ :=
            fun m n τ => ∏ t : Fin n, Q m t (fun s => τ (Fin.castLE t.2.le s)) (τ t)
          have hPsum : ∀ m n, ∑ τ, P m n τ = 1 := fun m n => hCausalSum Ω (Q m) (hQsum m) n
          have hPnonneg : ∀ m, (∀ i c, m i c ∈ Set.Icc (0 : ℝ) 1) → ∀ n τ, 0 ≤ P m n τ := by
            intro m hm n τ
            exact Finset.prod_nonneg (fun t _ => hQnonneg m hm _ _ _)
          have hPSupport : ∀ (m r : Fin K → Fin C → ℝ),
              (∀ i c, 0 < m i c ∧ m i c < 1) → (∀ i c, 0 < r i c ∧ r i c < 1) →
              ∀ n τ, P m n τ = 0 ↔ P r n τ = 0 := by
            intro m r hm hr n τ
            simp only [P, Finset.prod_eq_zero_iff]
            constructor
            · rintro ⟨t, ht, hz⟩
              exact ⟨t, ht, (hQSupport m r hm hr _ _ _).1 hz⟩
            · rintro ⟨t, ht, hz⟩
              exact ⟨t, ht, (hQSupport m r hm hr _ _ _).2 hz⟩
          let base : (Fin C → Fin K) → Fin C → Fin K → Fin C → ℝ :=
            fun b c i d => if d = c then 1 / 2 else p b i d
          have hpOpen : ∀ b i c, 0 < p b i c ∧ p b i c < 1 := by
            intro b i c
            dsimp [p]
            split_ifs <;> constructor <;> linarith [(hδ c).1, (hδ c).2]
          have hbaseOpen : ∀ b c i d, 0 < base b c i d ∧ base b c i d < 1 := by
            intro b c i d
            dsimp [base]
            split_ifs
            · constructor <;> norm_num
            · exact hpOpen b i d
          let κ : Fin C → ℝ := fun c =>
            (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (1 / 2 + δ c)) +
              (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) / (1 / 2 - δ c))
          have hκ : ∀ c, κ c ≤ 4 * δ c ^ 2 := fun c => hCoinKL (δ c) (hδ c).1 (hδ c).2
          have hUnchanged : ∀ b c j i d, d ≠ c ∨ i ≠ j →
              base b c i d = p (Function.update b c j) i d := by
            intro b c j i d hd
            rcases hd with hd | hi
            · simp [base, p, hd, Function.update_of_ne hd]
            · by_cases hd : d = c
              · subst d
                simp [base, p, hi]
              · simp [base, p, hd, Function.update_of_ne hd]
          have hBitSupport : ∀ (m r : Fin K → Fin C → ℝ),
              (∀ i c, 0 < m i c ∧ m i c < 1) → (∀ i c, 0 < r i c ∧ r i c < 1) →
              ∀ x i d v, bit m x i d v = 0 ↔ bit r x i d v = 0 := by
            intro m r hm hr x i d v
            by_cases hg : G x d
            · simp [bit, hg, ne_of_gt (hcoinPos _ (hm i d).1 (hm i d).2 v),
                ne_of_gt (hcoinPos _ (hr i d).1 (hr i d).2 v)]
            · simp only [bit, if_neg hg]
          have hBitsKL : ∀ b c j x i,
              (∑ v : Fin C → Bool, (∏ d, bit (base b c) x i d (v d)) *
                Real.log ((∏ d, bit (base b c) x i d (v d)) /
                  (∏ d, bit (p (Function.update b c j)) x i d (v d)))) =
              if i = j ∧ G x c then κ c else 0 := by
            intro b c j x i
            rw [hProductKL C _ _ (hbitNorm _ _ _) (hbitNorm _ _ _)
              (hBitSupport _ _ (hbaseOpen b c) (hpOpen _) x i)]
            by_cases hi : i = j
            · subst i
              rw [Finset.sum_eq_single c]
              · by_cases hg : G x c
                · norm_num [bit, base, p, hg, coin, κ, Fintype.sum_bool, sub_add_eq_sub_sub]
                · simp [bit, hg]
              · intro d hd hdc
                have heq : ∀ v, bit (base b c) x j d v =
                    bit (p (Function.update b c j)) x j d v := by
                  intro v
                  simp only [bit, hUnchanged b c j j d (Or.inl hdc)]
                simp_rw [heq, Real.log_div_self, mul_zero]
                simp
              · simp
            · have heq : ∀ d v, bit (base b c) x i d v =
                  bit (p (Function.update b c j)) x i d v := by
                intro d v
                simp only [bit, hUnchanged b c j i d (Or.inr hi)]
              simp_rw [heq, Real.log_div_self, mul_zero]
              simp [hi]
          have hQKL : ∀ b c j t h,
              (∑ o, Q (base b c) t h o *
                Real.log (Q (base b c) t h o / Q (p (Function.update b c j)) t h o)) =
              κ c * ∑ x ∈ Finset.univ.filter (fun x => G x c), D x * A t (decode t h) x j := by
            intro b c j t h
            have hscalar (x : Fin C) (i : Fin K) (v : Fin C → Bool) :
                (D x * A t (decode t h) x i * ∏ d, bit (base b c) x i d (v d)) *
                  Real.log ((D x * A t (decode t h) x i * ∏ d, bit (base b c) x i d (v d)) /
                    (D x * A t (decode t h) x i * ∏ d, bit (p (Function.update b c j)) x i d (v d))) =
                D x * A t (decode t h) x i *
                  ((∏ d, bit (base b c) x i d (v d)) *
                    Real.log ((∏ d, bit (base b c) x i d (v d)) /
                      (∏ d, bit (p (Function.update b c j)) x i d (v d)))) := by
              simpa only [Real.log_div_self, mul_zero, zero_add] using
                hScalarKL (D x * A t (decode t h) x i) (D x * A t (decode t h) x i)
                  _ _ Iff.rfl (hBitsSupport _ _ (hbaseOpen b c) (hpOpen _) x i v)
            calc
              _ = ∑ x : Fin C, ∑ i : Fin K, D x * A t (decode t h) x i *
                  (∑ v : Fin C → Bool, (∏ d, bit (base b c) x i d (v d)) *
                    Real.log ((∏ d, bit (base b c) x i d (v d)) /
                      (∏ d, bit (p (Function.update b c j)) x i d (v d)))) := by
                change (∑ o : Fin C × (Fin K × (Fin C → Bool)),
                  (D o.1 * A t (decode t h) o.1 o.2.1 * ∏ d, bit (base b c) o.1 o.2.1 d (o.2.2 d)) *
                    Real.log ((D o.1 * A t (decode t h) o.1 o.2.1 * ∏ d, bit (base b c) o.1 o.2.1 d (o.2.2 d)) /
                      (D o.1 * A t (decode t h) o.1 o.2.1 * ∏ d, bit (p (Function.update b c j)) o.1 o.2.1 d (o.2.2 d)))) = _
                simp_rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro x hx
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun v _ => hscalar x i v)
              _ = ∑ x : Fin C, ∑ i : Fin K, D x * A t (decode t h) x i *
                  (if i = j ∧ G x c then κ c else 0) := by simp_rw [hBitsKL]
              _ = ∑ x : Fin C, if G x c then D x * A t (decode t h) x j * κ c else 0 := by
                apply Finset.sum_congr rfl
                intro x hx
                by_cases hg : G x c <;> simp [hg]
              _ = _ := by
                rw [Finset.mul_sum, Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro x hx
                split_ifs <;> ring
          have hInfo : ∀ b c,
              (∑ j : Fin K, ∑ τ : Fin T → Ω, P (base b c) T τ *
                Real.log (P (base b c) T τ / P (p (Function.update b c j)) T τ)) ≤ (K : ℝ) / 64 := by
            intro b c
            let q : ℝ := ∑ x ∈ Finset.univ.filter (fun x => G x c), D x
            have hq : 0 ≤ q := Finset.sum_nonneg (fun x _ => hD.1 x)
            have hKL : (∑ j : Fin K, ∑ τ : Fin T → Ω, P (base b c) T τ *
                Real.log (P (base b c) T τ / P (p (Function.update b c j)) T τ)) = κ c * T * q := by
              calc
                _ = ∑ j : Fin K, ∑ t : Fin T, ∑ h : Fin (t : ℕ) → Ω,
                    P (base b c) t h * (κ c *
                      ∑ x ∈ Finset.univ.filter (fun x => G x c), D x * A t (decode t h) x j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hk := hCausalKL Ω (Q (base b c)) (Q (p (Function.update b c j)))
                    (hQsum _) (hQsum _) (hQSupport _ _ (hbaseOpen b c) (hpOpen _)) T
                  change (∑ τ, P (base b c) T τ *
                    Real.log (P (base b c) T τ / P (p (Function.update b c j)) T τ)) = _
                  rw [hk]
                  simp_rw [hQKL]
                  rfl
                _ = ∑ t : Fin T, ∑ h : Fin (t : ℕ) → Ω, P (base b c) t h * (κ c * q) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro t ht
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro h hh
                  have hcount : (∑ j : Fin K, ∑ x ∈ Finset.univ.filter (fun x => G x c),
                      D x * A t (decode t h) x j) = q := by
                    rw [Finset.sum_comm]
                    simp_rw [← Finset.mul_sum, hA.2, mul_one]
                    rfl
                  rw [← Finset.mul_sum, ← Finset.mul_sum, hcount]
                _ = κ c * T * q := by
                  have hs : ∀ t : Fin T,
                      (∑ h : Fin (t : ℕ) → Ω, P (base b c) t h * (κ c * q)) = κ c * q := by
                    intro t
                    rw [← Finset.sum_mul, hPsum, one_mul]
                  simp_rw [hs]
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                  ring
            rw [hKL]
            calc
              _ ≤ (4 * δ c ^ 2) * T * q :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (hκ c) (Nat.cast_nonneg T)) hq
              _ ≤ (K : ℝ) / 64 := by have hs := hsmall c; change δ c ^ 2 * T * q ≤ _ at hs; linarith
          have hCorrect : ∀ b c (t : Fin T),
              (∑ j : Fin K, ∑ τ : Fin T → Ω, P (p (Function.update b c j)) T τ *
                A t (decode t (fun s => τ (Fin.castLE t.2.le s))) c j) ≤ 3 * (K : ℝ) / 4 := by
            intro b c t
            apply hMultiTest K hK (Fin T → Ω) (P (base b c) T)
              (fun j => P (p (Function.update b c j)) T)
            · exact hPnonneg _ (fun i d => ⟨(hbaseOpen b c i d).1.le, (hbaseOpen b c i d).2.le⟩) T
            · intro j
              exact hPnonneg _ (hp _) T
            · exact hPsum _ T
            · intro j
              exact hPsum _ T
            · intro j
              exact hPSupport _ _ (hbaseOpen b c) (hpOpen _) T
            · intro j τ
              exact hA.1 _ _ _ _
            · intro τ
              exact hA.2 _ _ _
            · exact hInfo b c
          have hUpdateSum : ∀ (f : (Fin C → Fin K) → ℝ) (c : Fin C),
              (∑ b : Fin C → Fin K, ∑ j : Fin K, f (Function.update b c j)) =
              (K : ℝ) * ∑ b : Fin C → Fin K, f b := by
            intro f c
            let e := Equiv.funSplitAt c (Fin K)
            have heq : ∀ (z : Fin K × ({d : Fin C // d ≠ c} → Fin K)) (j : Fin K),
                Function.update (e.symm z) c j = e.symm (j, z.2) := by
              intro z j
              funext d
              by_cases hd : d = c
              · subst d
                simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
              · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hd, Function.update_of_ne hd]
            calc
              _ = ∑ z : Fin K × ({d : Fin C // d ≠ c} → Fin K),
                  ∑ j : Fin K, f (Function.update (e.symm z) c j) := by
                exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm
              _ = ∑ z : Fin K × ({d : Fin C // d ≠ c} → Fin K),
                  ∑ j : Fin K, f (e.symm (j, z.2)) := by simp_rw [heq]
              _ = (K : ℝ) * (∑ h : {d : Fin C // d ≠ c} → Fin K, ∑ j : Fin K, f (e.symm (j, h))) := by
                rw [Fintype.sum_prod_type]
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              _ = (K : ℝ) * (∑ j : Fin K, ∑ h : {d : Fin C // d ≠ c} → Fin K, f (e.symm (j, h))) := by
                rw [Finset.sum_comm]
              _ = _ := by
                congr 1
                calc
                  _ = ∑ z : Fin K × ({d : Fin C // d ≠ c} → Fin K), f (e.symm z) :=
                    (Fintype.sum_prod_type (fun z : Fin K × ({d : Fin C // d ≠ c} → Fin K) => f (e.symm z))).symm
                  _ = _ := Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
          let F : Fin C → Fin T → (Fin C → Fin K) → ℝ := fun c t b =>
            ∑ τ : Fin T → Ω, P (p b) T τ *
              A t (decode t (fun s => τ (Fin.castLE t.2.le s))) c (b c)
          let N : ℝ := Fintype.card (Fin C → Fin K)
          have hAvgCorrect : ∀ c t, (∑ b, F c t b) ≤ 3 * N / 4 := by
            intro c t
            have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hCorrect b c t)
            have heq : (∑ b : Fin C → Fin K, ∑ j : Fin K,
                ∑ τ : Fin T → Ω, P (p (Function.update b c j)) T τ *
                  A t (decode t (fun s => τ (Fin.castLE t.2.le s))) c j) =
                (K : ℝ) * ∑ b, F c t b := by
              simpa only [F, Function.update_self] using hUpdateSum (F c t) c
            rw [heq] at hs
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
            have hKpos : (0 : ℝ) < K := Nat.cast_pos.2 (NeZero.pos K)
            apply (mul_le_mul_iff_right₀ hKpos).1
            calc
              _ ≤ (Fintype.card (Fin C → Fin K) : ℝ) * (3 * (K : ℝ) / 4) := hs
              _ = _ := by dsimp [N]; ring
          suffices hAvg : (Fintype.card (Fin C → Fin K) : ℝ) *
              ((T : ℝ) / 8 * (∑ c, D c * δ c)) ≤
              ∑ b : Fin C → Fin K, stochRegret T (fun _ => G) (S b) A by
            by_contra hnone
            have hall : ∀ b : Fin C → Fin K,
                stochRegret T (fun _ => G) (S b) A < (T : ℝ) / 8 * (∑ c, D c * δ c) := by
              intro b
              apply lt_of_not_ge
              intro hb
              exact hnone ⟨S b, hind b, hSD b, hb⟩
            have hsumlt := Finset.sum_lt_sum (s := Finset.univ)
              (fun b _ => (hall b).le) ⟨(fun _ => (0 : Fin K)), Finset.mem_univ _, hall _⟩
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumlt
            linarith
          suffices hRegret : ∀ b, stochRegret T (fun _ => G) (S b) A =
              ∑ t : Fin T, ∑ c : Fin C, D c * δ c * (1 - F c t b) by
            have hN : 0 ≤ N := Nat.cast_nonneg _
            have hsumδ : 0 ≤ ∑ c, D c * δ c :=
              Finset.sum_nonneg (fun c _ => mul_nonneg (hD.1 c) (hδ c).1)
            change N * ((T : ℝ) / 8 * ∑ c, D c * δ c) ≤ _
            calc
              _ ≤ N * ((T : ℝ) / 4 * ∑ c, D c * δ c) := by
                nlinarith [mul_nonneg hN (mul_nonneg (Nat.cast_nonneg T) hsumδ)]
              _ = ∑ t : Fin T, ∑ c : Fin C, D c * δ c * (N / 4) := by
                simp_rw [← Finset.sum_mul]
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring
              _ ≤ ∑ t : Fin T, ∑ c : Fin C, D c * δ c * (N - ∑ b, F c t b) := by
                apply Finset.sum_le_sum
                intro t ht
                apply Finset.sum_le_sum
                intro c hc
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hD.1 c) (hδ c).1)
                linarith [hAvgCorrect c t]
              _ = ∑ b, stochRegret T (fun _ => G) (S b) A := by
                simp_rw [hRegret]
                conv_rhs => rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro t ht
                conv_rhs => rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro c hc
                rw [← Finset.mul_sum, Finset.sum_sub_distrib]
                simp [N]
          intro b
          have hsup : ∀ c, Finset.univ.sup' Finset.univ_nonempty (fun i => (S b).mean i c) =
              1 / 2 + δ c := by
            intro c
            rw [hmean b]
            apply le_antisymm
            · apply Finset.sup'_le
              intro i hi
              dsimp [p]
              split_ifs <;> linarith [(hδ c).1]
            · calc
                (1 / 2 : ℝ) + δ c = p b (b c) c := by simp only [p, ite_true]
                _ ≤ _ := Finset.le_sup' (s := Finset.univ)
                  (f := fun i => p b i c) (Finset.mem_univ (b c))
          have hbest : (∑ c, (S b).D c * Finset.univ.sup' Finset.univ_nonempty
              (fun i => (S b).mean i c)) = 1 / 2 + ∑ c, D c * δ c := by
            simp_rw [hSD b, hsup, mul_add]
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hD.2]
            ring
          suffices hIntegral : (∫ r, algReward (fun _ : Fin K => G) D A r ∂((S b).tableLaw T)) =
              (T : ℝ) / 2 + ∑ t : Fin T, ∑ c : Fin C, D c * δ c * F c t b by
            unfold stochRegret
            rw [hbest, hSD b, hIntegral]
            have hRHS : (∑ t : Fin T, ∑ c : Fin C, D c * δ c * (1 - F c t b)) =
                (T : ℝ) * (∑ c, D c * δ c) - ∑ t : Fin T, ∑ c : Fin C, D c * δ c * F c t b := by
              simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [hRHS]
            ring
          let e₀ : Bool → ℝ := fun v => if v then 1 else 0
          have he₀ : Measurable e₀ := Measurable.of_discrete
          let μ₀ : Fin K → Fin C → MeasureTheory.Measure Bool := fun i c =>
            ProbabilityTheory.bernoulliMeasure true false ⟨p b i c, hp b i c⟩
          let μ₁ : Fin K → MeasureTheory.Measure (Fin C → Bool) :=
            fun i => MeasureTheory.Measure.pi (μ₀ i)
          let μ₂ : MeasureTheory.Measure (Fin K → Fin C → Bool) := MeasureTheory.Measure.pi μ₁
          let μ : MeasureTheory.Measure (Fin T → Fin K → Fin C → Bool) :=
            MeasureTheory.Measure.pi (fun _ => μ₂)
          let enc : (Fin T → Fin K → Fin C → Bool) → Fin T → Fin K → Fin C → ℝ :=
            fun z t i c => e₀ (z t i c)
          letI : ∀ i c, MeasureTheory.IsProbabilityMeasure ((S b).F i c) := (S b).F_prob
          letI : ∀ t, MeasureTheory.IsProbabilityMeasure ((S b).roundLaw t) := (S b).round_prob
          have hPres₀ : ∀ i c, MeasureTheory.MeasurePreserving e₀ (μ₀ i c) ((S b).F i c) := by
            intro i c
            refine ⟨he₀, ?_⟩
            rw [hF b]
            simpa [μ₀, e₀] using ProbabilityTheory.map_bernoulliMeasure true false e₀ ⟨p b i c, hp b i c⟩
          have hPres₁ : ∀ i, MeasureTheory.MeasurePreserving
              (fun z : Fin C → Bool => fun c => e₀ (z c)) (μ₁ i)
              (MeasureTheory.Measure.pi ((S b).F i)) := by
            intro i
            exact MeasureTheory.measurePreserving_pi _ _ (hPres₀ i)
          have hPres₂ : MeasureTheory.MeasurePreserving
              (fun z : Fin K → Fin C → Bool => fun i c => e₀ (z i c)) μ₂
              (MeasureTheory.Measure.pi (fun i => MeasureTheory.Measure.pi ((S b).F i))) :=
            MeasureTheory.measurePreserving_pi _ _ hPres₁
          have hPresRound : ∀ t, MeasureTheory.MeasurePreserving
              (fun z : Fin K → Fin C → Bool => fun i c => e₀ (z i c)) μ₂ ((S b).roundLaw t) := by
            intro t
            rw [hind b t]
            exact hPres₂
          have hPres : MeasureTheory.MeasurePreserving enc μ ((S b).tableLaw T) :=
            MeasureTheory.measurePreserving_pi _ _ (fun t : Fin T => hPresRound t)
          have hAtom : ∀ i c v, (μ₀ i c).real {v} = coin (p b i c) v := by
            intro i c v
            cases v <;> simp [μ₀, coin, ProbabilityTheory.bernoulliMeasure_real_apply]
          have hMass : ∀ z : Fin T → Fin K → Fin C → Bool,
              μ.real {z} = ∏ t, ∏ i, ∏ c, coin (p b i c) (z t i c) := by
            intro z
            simp only [μ, μ₂, μ₁, MeasureTheory.measureReal_def,
              MeasureTheory.Measure.pi_singleton, ENNReal.toReal_prod]
            simp only [← MeasureTheory.measureReal_def, hAtom]
          have hExplicit : (∫ r, algReward (fun _ : Fin K => G) D A r ∂((S b).tableLaw T)) =
              ∑ z : Fin T → Fin K → Fin C → Bool,
                (∏ t, ∏ i, ∏ c, coin (p b i c) (z t i c)) *
                  algReward (fun _ : Fin K => G) D A (enc z) := by
            rw [← hPres.map_eq, MeasureTheory.integral_map_of_stronglyMeasurable hPres.measurable
              (hAlgMeasurable K C T (fun _ => G) D A hAm).stronglyMeasurable]
            simpa only [smul_eq_mul, hMass] using
              (MeasureTheory.integral_fintype (μ := μ)
                (f := fun z => algReward (fun _ : Fin K => G) D A (enc z))
                MeasureTheory.Integrable.of_finite)
          let η : Fin C → Fin K → Fin C → MeasureTheory.Measure Bool :=
            fun x i d => if G x d then μ₀ i d else MeasureTheory.Measure.dirac false
          have hηprob : ∀ x i d, MeasureTheory.IsProbabilityMeasure (η x i d) := by
            intro x i d
            dsimp [η]
            split_ifs <;> infer_instance
          letI : ∀ x i d, MeasureTheory.IsProbabilityMeasure (η x i d) := hηprob
          let mask : Fin C → (Fin C → Bool) → Fin C → Bool :=
            fun x z d => if G x d then z d else false
          have hMask₀ : ∀ x i d, MeasureTheory.MeasurePreserving
              (fun v : Bool => if G x d then v else false) (μ₀ i d) (η x i d) := by
            intro x i d
            by_cases hg : G x d
            · refine ⟨Measurable.of_discrete, ?_⟩
              simp only [η, if_pos hg]
              exact MeasureTheory.Measure.map_id
            · refine ⟨Measurable.of_discrete, ?_⟩
              simp [η, hg, MeasureTheory.Measure.map_const]
              rw [show ({false, true} : Set Bool) = Set.univ by ext v; cases v <;> simp,
                MeasureTheory.measure_univ, one_smul]
          have hMask₁ : ∀ x i, MeasureTheory.MeasurePreserving (mask x) (μ₁ i)
              (MeasureTheory.Measure.pi (η x i)) := by
            intro x i
            exact MeasureTheory.measurePreserving_pi _ _ (hMask₀ x i)
          have hMask₂ : ∀ x i, MeasureTheory.MeasurePreserving
              (fun z : Fin K → Fin C → Bool => mask x (z i)) μ₂
              (MeasureTheory.Measure.pi (η x i)) := by
            intro x i
            exact (hMask₁ x i).comp (MeasureTheory.measurePreserving_eval μ₁ i)
          let maskTable : (Fin T → Fin C × Fin K) →
              (Fin T → Fin K → Fin C → Bool) → Fin T → Fin C → Bool :=
            fun τ z t => mask (τ t).1 (z t (τ t).2)
          let ν : (Fin T → Fin C × Fin K) → MeasureTheory.Measure (Fin T → Fin C → Bool) :=
            fun τ => MeasureTheory.Measure.pi (fun t => MeasureTheory.Measure.pi (η (τ t).1 (τ t).2))
          have hMaskTable : ∀ τ, MeasureTheory.MeasurePreserving (maskTable τ) μ (ν τ) := by
            intro τ
            exact MeasureTheory.measurePreserving_pi _ _ (fun t => hMask₂ (τ t).1 (τ t).2)
          have hηAtom : ∀ x i d v, (η x i d).real {v} = bit (p b) x i d v := by
            intro x i d v
            by_cases hg : G x d
            · simpa [η, bit, hg] using hAtom i d v
            · cases v <;> simp [η, hg, bit, MeasureTheory.measureReal_def]
          have hνMass : ∀ τ (v : Fin T → Fin C → Bool),
              (ν τ).real {v} = ∏ t, ∏ d, bit (p b) (τ t).1 (τ t).2 d (v t d) := by
            intro τ v
            simp only [ν, MeasureTheory.measureReal_def,
              MeasureTheory.Measure.pi_singleton, ENNReal.toReal_prod]
            simp only [← MeasureTheory.measureReal_def, hηAtom]
          let join : (Fin T → Fin C × Fin K) → (Fin T → Fin C → Bool) → Fin T → Ω :=
            fun τ v t => ((τ t).1, (τ t).2, v t)
          let H : (Fin T → Fin C × Fin K) → (Fin T → Fin C → Bool) → ℝ := fun τ v =>
            (∏ t : Fin T, D (τ t).1 *
              A t (decode t (fun s => join τ v (Fin.castLE t.2.le s))) (τ t).1 (τ t).2) *
              ∑ t : Fin T, e₀ (v t (τ t).1)
          have hHistMask : ∀ τ z (t : Fin T),
              hist (fun _ : Fin K => G) (enc z) τ t =
                decode t (fun s => join τ (maskTable τ z) (Fin.castLE t.2.le s)) := by
            intro τ z t
            funext s
            dsimp [hist, decode, join]
            apply congrArg (fun r : Fin C → ℝ =>
              ((τ (Fin.castLE t.2.le s)).1, (τ (Fin.castLE t.2.le s)).2, r))
            funext d
            dsimp [feedback, maskTable, mask, enc]
            by_cases hg : G (τ (Fin.castLE t.2.le s)).1 d <;> simp [hg, e₀]
          have hRewardMask : ∀ τ z,
              (∑ t : Fin T, enc z t (τ t).2 (τ t).1) =
                ∑ t : Fin T, e₀ (maskTable τ z t (τ t).1) := by
            intro τ z
            apply Finset.sum_congr rfl
            intro t ht
            simp [enc, maskTable, mask, hG]
          have hFullEq : ∀ τ z,
              trajProb (fun _ : Fin K => G) D A (enc z) τ *
                (∑ t : Fin T, enc z t (τ t).2 (τ t).1) = H τ (maskTable τ z) := by
            intro τ z
            unfold trajProb
            simp_rw [hHistMask, hRewardMask]
            rfl
          have hGroup : ∀ τ,
              (∑ z : Fin T → Fin K → Fin C → Bool, μ.real {z} * H τ (maskTable τ z)) =
                ∑ v : Fin T → Fin C → Bool, (ν τ).real {v} * H τ v := by
            intro τ
            calc
              _ = ∫ z, H τ (maskTable τ z) ∂μ := by
                symm
                simpa only [smul_eq_mul] using
                  (MeasureTheory.integral_fintype (μ := μ) (f := fun z => H τ (maskTable τ z))
                    MeasureTheory.Integrable.of_finite)
              _ = ∫ v, H τ v ∂(ν τ) := by
                rw [← (hMaskTable τ).map_eq,
                  MeasureTheory.integral_map_of_stronglyMeasurable (hMaskTable τ).measurable
                    (Measurable.of_discrete : Measurable (H τ)).stronglyMeasurable]
              _ = _ := by
                simpa only [smul_eq_mul] using
                  (MeasureTheory.integral_fintype (μ := ν τ) (f := H τ) MeasureTheory.Integrable.of_finite)
          have hObserved : (∫ r, algReward (fun _ : Fin K => G) D A r ∂((S b).tableLaw T)) =
              ∑ τ : Fin T → Fin C × Fin K, ∑ v : Fin T → Fin C → Bool,
                (ν τ).real {v} * H τ v := by
            rw [hExplicit]
            unfold algReward expect
            conv_lhs => arg 2; ext z; rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [← hGroup]
            apply Finset.sum_congr rfl
            intro z hz
            rw [hMass, hFullEq]
          let E : ((Fin T → Fin C × Fin K) × (Fin T → Fin C → Bool)) ≃ (Fin T → Ω) := {
            toFun := fun z => join z.1 z.2
            invFun := fun o => (fun t => ((o t).1, (o t).2.1), fun t => (o t).2.2)
            left_inv := by
              intro z
              apply Prod.ext
              · funext t
                exact Prod.eta _
              · rfl
            right_inv := by
              intro o
              funext t
              exact Prod.eta _
          }
          have hJoinWeight : ∀ τ v,
              (ν τ).real {v} * H τ v =
                P (p b) T (join τ v) * ∑ t : Fin T, e₀ (v t (τ t).1) := by
            intro τ v
            rw [hνMass]
            simp only [H, P, Q, join, Finset.prod_mul_distrib]
            ring
          have hPath : (∑ τ : Fin T → Fin C × Fin K, ∑ v : Fin T → Fin C → Bool,
              (ν τ).real {v} * H τ v) =
              ∑ o : Fin T → Ω, P (p b) T o * ∑ t : Fin T, e₀ ((o t).2.2 (o t).1) := by
            calc
              _ = ∑ z : (Fin T → Fin C × Fin K) × (Fin T → Fin C → Bool),
                  (ν z.1).real {z.2} * H z.1 z.2 :=
                (Fintype.sum_prod_type (fun z : (Fin T → Fin C × Fin K) × (Fin T → Fin C → Bool) =>
                  (ν z.1).real {z.2} * H z.1 z.2)).symm
              _ = _ := Fintype.sum_equiv E _ _ (fun z => by rw [hJoinWeight]; rfl)
          have hBitMean : ∀ x i,
              (∑ v : Fin C → Bool, (∏ d, bit (p b) x i d (v d)) * e₀ (v x)) = p b i x := by
            intro x i
            let μbit : MeasureTheory.Measure (Fin C → Bool) := MeasureTheory.Measure.pi (η x i)
            have hBitMass : ∀ v, μbit.real {v} = ∏ d, bit (p b) x i d (v d) := by
              intro v
              simp only [μbit, MeasureTheory.measureReal_def, MeasureTheory.Measure.pi_singleton,
                ENNReal.toReal_prod]
              simp only [← MeasureTheory.measureReal_def, hηAtom]
            have hEval := MeasureTheory.measurePreserving_eval (η x i) x
            calc
              _ = ∫ v, e₀ (v x) ∂μbit := by
                symm
                simpa only [smul_eq_mul, hBitMass] using
                  (MeasureTheory.integral_fintype (μ := μbit) (f := fun v => e₀ (v x))
                    MeasureTheory.Integrable.of_finite)
              _ = ∫ v, e₀ v ∂(η x i x) := by
                rw [← hEval.map_eq,
                  MeasureTheory.integral_map_of_stronglyMeasurable hEval.measurable he₀.stronglyMeasurable]
              _ = _ := by
                simp [η, hG, μ₀, ProbabilityTheory.integral_bernoulliMeasure, e₀]
          let M : (t : ℕ) → (Fin t → Ω) → ℝ := fun t h =>
            ∑ x : Fin C, D x * ∑ i : Fin K, A t (decode t h) x i * p b i x
          have hStepReward : ∀ t h,
              (∑ o : Ω, Q (p b) t h o * e₀ (o.2.2 o.1)) = M t h := by
            intro t h
            change (∑ o : Fin C × (Fin K × (Fin C → Bool)),
              (D o.1 * A t (decode t h) o.1 o.2.1 * ∏ d, bit (p b) o.1 o.2.1 d (o.2.2 d)) *
                e₀ (o.2.2 o.1)) = _
            simp_rw [Fintype.sum_prod_type]
            change (∑ x : Fin C, ∑ i : Fin K, ∑ v : Fin C → Bool,
              (D x * A t (decode t h) x i * ∏ d, bit (p b) x i d (v d)) * e₀ (v x)) = M t h
            calc
              _ = ∑ x : Fin C, ∑ i : Fin K, D x * A t (decode t h) x i *
                  (∑ v : Fin C → Bool, (∏ d, bit (p b) x i d (v d)) * e₀ (v x)) := by
                apply Finset.sum_congr rfl
                intro x hx
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro v hv
                ring
              _ = M t h := by
                simp_rw [hBitMean]
                dsimp [M]
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
          let Y : (t : ℕ) → (Fin t → Ω) → Ω → ℝ := fun t h o => e₀ (o.2.2 o.1) - M t h
          have hY : ∀ t h, ∑ o, Q (p b) t h o * Y t h o = 0 := by
            intro t h
            dsimp [Y]
            simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
            rw [hStepReward, hQsum, one_mul, sub_self]
          have hExpected :
              (∑ o : Fin T → Ω, P (p b) T o * ∑ t : Fin T, e₀ ((o t).2.2 (o t).1)) =
              ∑ o : Fin T → Ω, P (p b) T o *
                ∑ t : Fin T, M t (fun s => o (Fin.castLE t.2.le s)) := by
            have hm := hMartingale Ω (Q (p b)) Y (hQsum _) hY T
            change (∑ o : Fin T → Ω, P (p b) T o *
              ∑ t : Fin T, Y t (fun s => o (Fin.castLE t.2.le s)) (o t)) = 0 at hm
            dsimp [Y] at hm
            simp_rw [Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib] at hm
            exact sub_eq_zero.1 hm
          have hM : ∀ t h, M t h = 1 / 2 + ∑ c : Fin C,
              D c * δ c * A t (decode t h) c (b c) := by
            intro t h
            have hArm : ∀ c, (∑ i : Fin K, A t (decode t h) c i * p b i c) =
                1 / 2 + δ c * A t (decode t h) c (b c) := by
              intro c
              dsimp [p]
              simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
              rw [hA.2, one_mul]
              simp [mul_ite, mul_zero, mul_comm]
            dsimp [M]
            simp_rw [hArm, mul_add, Finset.sum_add_distrib]
            rw [← Finset.sum_mul, hD.2, one_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro c hc
            ring
          have hMeanExpected :
              (∑ o : Fin T → Ω, P (p b) T o *
                ∑ t : Fin T, M t (fun s => o (Fin.castLE t.2.le s))) =
              (T : ℝ) / 2 + ∑ t : Fin T, ∑ c : Fin C, D c * δ c * F c t b := by
            calc
              _ = ∑ t : Fin T, ∑ o : Fin T → Ω, P (p b) T o *
                  M t (fun s => o (Fin.castLE t.2.le s)) := by
                conv_lhs => arg 2; ext o; rw [Finset.mul_sum]
                rw [Finset.sum_comm]
              _ = ∑ t : Fin T, ((1 / 2 : ℝ) + ∑ c : Fin C, D c * δ c * F c t b) := by
                apply Finset.sum_congr rfl
                intro t ht
                simp_rw [hM, mul_add, Finset.sum_add_distrib]
                rw [← Finset.sum_mul, hPsum, one_mul]
                congr 1
                conv_lhs => arg 2; ext o; rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro c hc
                dsimp [F]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro o ho
                ring
              _ = _ := by
                rw [Finset.sum_add_distrib]
                simp [Finset.sum_const, Fintype.card_fin] <;> ring
          rw [hObserved, hPath, hExpected, hMeanExpected]
