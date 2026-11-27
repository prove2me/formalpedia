-- Prove2me | solution 1 for FakeUserRanking.FORC.Supplement.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:43.63112+00:00
-- url     : https://prove2.me/submissions/9581bd09-a646-41f9-987d-b1873268c0cf

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR
import Definitions.Def_FakeUserRanking_FORC_Supplement_EventE
import Definitions.Def_FakeUserRanking_FORC_Supplement_Gamma

open FakeUserRanking
open FakeUserRanking.FORC
open FakeUserRanking.FORC.Supplement

/-- Lemma 3 (Properties of the Graph G under Event E), p. 22, pathwise: on every trajectory in
`E`, for products `j < i` (paper: `i > j`, so `μ_j > μ_i`), (1) FAR's graph never holds the
incorrect edge `(j, i)`, and (2) once `η_{i,t}, η_{j,t} ≥ γ_{j,i}` at the end of round `t`, the
graph holds the correct edge `(i, j)` at the end of every round `t' ≥ t`. -/
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n 1) (hE : eventE inst T F tb fb τ) (j i : Fin n) (hji : j < i) :
    (∀ t : ℕ, t ≤ T → (j, i) ∉ (farStateAt n T F tb fb τ t).graph) ∧
    (∀ t : ℕ, t ≤ T →
      gamma13 T F inst j i ≤ ((farStateAt n T F tb fb τ t).cnt i : ℝ) →
      gamma13 T F inst j i ≤ ((farStateAt n T F tb fb τ t).cnt j : ℝ) →
      ∀ t' : ℕ, t ≤ t' → t' ≤ T → (i, j) ∈ (farStateAt n T F tb fb τ t').graph) := by
        have hstep : ∀ t (ht : t < T), ∃ π, farStateAt n T F tb fb τ (t+1) =
            (farStateAt n T F tb fb τ t).update n T F π (τ ⟨t, ht⟩).2.2 := by
          intro t ht
          have hh : algHist τ (t+1) = algHist τ t ++ [((τ ⟨t,ht⟩).1, (τ ⟨t,ht⟩).2.2)] := by
            simp [algHist, List.take_add_one, ht]
          simp only [farStateAt]
          rw [hh, farState, farState, List.foldl_append]
          exact ⟨_, rfl⟩
        have hA : ∀ t (ht : t < T) (e : Fin n × Fin n), e ∈ (farStateAt n T F tb fb τ (t+1)).graph ↔
            e ∈ (farStateAt n T F tb fb τ t).graph ∨
              farEdgeCond n T F (farStateAt n T F tb fb τ (t+1)) e.1 e.2 := by
          intro t ht e
          obtain ⟨π, hπ⟩ := hstep t ht
          rw [hπ]
          simp only [FarState.update, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Iff.rfl
        have h0 : farStateAt n T F tb fb τ 0 = FarState.init := by
          simp [farStateAt, farState, algHist]
        have hmono : ∀ t e, e ∈ (farStateAt n T F tb fb τ t).graph → ∀ t', t ≤ t' → t' ≤ T →
            e ∈ (farStateAt n T F tb fb τ t').graph := by
          intro t e he t' htt'
          induction t', htt' using Nat.le_induction with
          | base => intro _; exact he
          | succ m hm ih =>
            intro hm1
            exact (hA m (by omega) e).2 (Or.inl (ih (by omega)))
        have hΔ : 0 < inst.μ j - inst.μ i := by have := hμ hji; linarith
        have hwin : ∀ t (st : FarState n), st.cnt t ≠ 0 → farWindow n T F st t = farRadius n T F st t := by
          intro t st h
          simp [farWindow, h]
        refine ⟨?_, ?_⟩
        · intro t ht
          induction t with
          | zero => rw [h0]; simp [FarState.init]
          | succ m ih =>
            intro hmem
            rcases (hA m (by omega) (j, i)).1 hmem with h | h
            · exact ih (by omega) h
            · obtain ⟨hcj, hci, hle⟩ := h
              have Ej := hE (m+1) (by omega) ht j
              have Ei := hE (m+1) (by omega) ht i
              dsimp only at hcj hci hle
              rw [hwin _ _ hcj.ne'] at Ej
              rw [hwin _ _ hci.ne'] at Ei
              linarith
        · intro t ht hγi hγj t' htt' ht'
          have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
          have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
          have hLg : 0 < Real.log (2 * n * T / farDelta n T) := by
            apply Real.log_pos
            rw [farDelta, div_div_eq_mul_div, div_one]
            have : (1:ℝ) ≤ n * T := by nlinarith
            nlinarith
          set Δ := inst.μ j - inst.μ i with hΔdef
          have hγ1 : 64 * Real.log (2 * n * T / farDelta n T) / Δ ^ 2 ≤ gamma13 T F inst j i :=
            le_max_left _ _
          have hγ2 : 8 * (F : ℝ) / Δ ≤ gamma13 T F inst j i := le_max_right _ _
          have hγpos : 0 < gamma13 T F inst j i := lt_of_lt_of_le (by positivity) hγ1
          have hrad : ∀ (st : FarState n) (k : Fin n), gamma13 T F inst j i ≤ (st.cnt k : ℝ) →
              farRadius n T F st k ≤ Δ / 4 := by
            intro st k hk
            have hη : 0 < (st.cnt k : ℝ) := lt_of_lt_of_le hγpos hk
            have h1 : 64 * Real.log (2 * n * T / farDelta n T) ≤ (st.cnt k : ℝ) * Δ ^ 2 := by
              rw [div_le_iff₀ (by positivity)] at hγ1; nlinarith [pow_pos hΔ 2]
            have h2 : 8 * (F : ℝ) ≤ (st.cnt k : ℝ) * Δ := by
              rw [div_le_iff₀ hΔ] at hγ2; nlinarith
            have hs : Real.sqrt (Real.log (2 * n * T / farDelta n T) / st.cnt k) ≤ Δ / 8 := by
              rw [← Real.sqrt_sq (by linarith : 0 ≤ Δ / 8)]
              apply Real.sqrt_le_sqrt
              rw [div_le_iff₀ hη]
              nlinarith
            have hf : (F : ℝ) / st.cnt k ≤ Δ / 8 := by
              rw [div_le_iff₀ hη]; nlinarith
            unfold farRadius
            linarith
          obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := by
            rcases t with _ | s
            · rw [h0] at hγi
              simp [FarState.init] at hγi
              linarith
            · exact ⟨s, rfl⟩
          have hci : 0 < (farStateAt n T F tb fb τ (s+1)).cnt i := by
            have : (0:ℝ) < (farStateAt n T F tb fb τ (s+1)).cnt i := lt_of_lt_of_le hγpos hγi
            exact_mod_cast this
          have hcj : 0 < (farStateAt n T F tb fb τ (s+1)).cnt j := by
            have : (0:ℝ) < (farStateAt n T F tb fb τ (s+1)).cnt j := lt_of_lt_of_le hγpos hγj
            exact_mod_cast this
          have Ej := hE (s+1) (by omega) ht j
          have Ei := hE (s+1) (by omega) ht i
          rw [hwin _ _ hcj.ne'] at Ej
          rw [hwin _ _ hci.ne'] at Ei
          have ri := hrad _ i hγi
          have rj := hrad _ j hγj
          have hedge : (i, j) ∈ (farStateAt n T F tb fb τ (s+1)).graph := by
            refine (hA s (by omega) (i, j)).2 (Or.inr ⟨hci, hcj, ?_⟩)
            dsimp only
            linarith
          exact hmono _ _ hedge t' htt' ht'
