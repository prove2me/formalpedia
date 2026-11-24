-- Prove2me | solution 1 for EliasGlobalClock.LowerBound.entropy_subadditivity
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:59:14.36288+00:00
-- url     : https://prove2.me/submissions/e85bbdf4-1b62-4e3d-aea7-e30f64bc9205

import Definitions.Def_EliasGlobalClock_LowerBound_finiteEntropy

open scoped BigOperators
open EliasGlobalClock.LowerBound

namespace EntAux

lemma sum_toReal {β : Type*} [Fintype β] (ν : PMF β) : ∑ b, (ν b).toReal = 1 := by
  have h := ν.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun b _ => ν.apply_ne_top b), h, ENNReal.toReal_one]

lemma marg {ℓ : ℕ} {S : Fin ℓ → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    (μ : PMF (∀ j, S j)) (j : Fin ℓ) (s : S j) :
    ((μ.map (fun z => z j)) s).toReal = ∑ z, if s = z j then (μ z).toReal else 0 := by
  rw [PMF.map_apply, tsum_fintype,
    ENNReal.toReal_sum (fun z _ => by split_ifs <;> simp [μ.apply_ne_top])]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp

lemma marg_log {ℓ : ℕ} {S : Fin ℓ → Type*} [∀ j, Fintype (S j)] (μ : PMF (∀ j, S j))
    (j : Fin ℓ) :
    ∑ s, ((μ.map (fun z => z j)) s).toReal * Real.log ((μ.map (fun z => z j)) s).toReal
      = ∑ z, (μ z).toReal * Real.log ((μ.map (fun z => z j)) (z j)).toReal := by
  classical
  have step : ∀ s : S j, ((μ.map (fun z => z j)) s).toReal *
      Real.log ((μ.map (fun z => z j)) s).toReal
      = ∑ z, if s = z j then
          (μ z).toReal * Real.log ((μ.map (fun z => z j)) (z j)).toReal else 0 := by
    intro s
    have h := marg μ j s
    calc _ = (∑ z, if s = z j then (μ z).toReal else 0) *
          Real.log ((μ.map (fun z => z j)) s).toReal := by rw [← h]
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun z _ => ?_
        split_ifs with hz
        · subst hz
          rfl
        · simp
  rw [Finset.sum_congr rfl (fun s _ => step s), Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp

end EntAux

theorem solution (ℓ : ℕ) (S : Fin ℓ → Type*) [∀ j, Fintype (S j)]
    (μ : PMF (∀ j, S j)) :
    finiteEntropy μ ≤ ∑ j : Fin ℓ, finiteEntropy (μ.map (fun z => z j)) := by
  classical
  have hR : ∑ j : Fin ℓ, finiteEntropy (μ.map (fun z => z j))
      = -∑ z, (μ z).toReal * ∑ j, Real.log ((μ.map (fun z => z j)) (z j)).toReal := by
    unfold finiteEntropy
    simp only [EntAux.marg_log, Finset.sum_neg_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hR]
  unfold finiteEntropy
  rw [neg_le_neg_iff]
  have key : ∀ z : (∀ j, S j),
      (μ z).toReal * ∑ j, Real.log ((μ.map (fun z => z j)) (z j)).toReal
        - (μ z).toReal * Real.log (μ z).toReal
      ≤ (∏ j, ((μ.map (fun z => z j)) (z j)).toReal) - (μ z).toReal := by
    intro z
    have hm0 : 0 ≤ (μ z).toReal := ENNReal.toReal_nonneg
    have hge : ∀ j, (μ z).toReal ≤ ((μ.map (fun z => z j)) (z j)).toReal := by
      intro j
      rw [EntAux.marg μ j (z j)]
      have := Finset.single_le_sum
        (f := fun z' : (∀ j, S j) => if z j = z' j then (μ z').toReal else 0)
        (fun z' _ => by split_ifs <;> simp) (Finset.mem_univ z)
      simpa using this
    rcases hm0.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [zero_mul, sub_zero]
      exact Finset.prod_nonneg (fun j _ => ENNReal.toReal_nonneg)
    · have hMpos : ∀ j, 0 < ((μ.map (fun z => z j)) (z j)).toReal :=
        fun j => lt_of_lt_of_le hpos (hge j)
      rw [← Real.log_prod (fun j _ => (hMpos j).ne')]
      set Pz := ∏ j, ((μ.map (fun z => z j)) (z j)).toReal with hPz
      have hP : 0 < Pz := Finset.prod_pos (fun j _ => hMpos j)
      have hl := Real.log_le_sub_one_of_pos (div_pos hP hpos)
      rw [Real.log_div hP.ne' hpos.ne'] at hl
      have h2 := mul_le_mul_of_nonneg_left hl hm0
      have h3 : (μ z).toReal * (Pz / (μ z).toReal) = Pz := by field_simp
      rw [mul_sub, mul_sub] at h2
      linarith
  have hsumP : ∑ z : (∀ j, S j), ∏ j, ((μ.map (fun z => z j)) (z j)).toReal = 1 := by
    have h := Finset.prod_univ_sum (fun j => (Finset.univ : Finset (S j)))
      (fun j s => ((μ.map (fun z => z j)) s).toReal)
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    exact Finset.prod_eq_one (fun j _ => EntAux.sum_toReal _)
  have htot := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => key z)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumP, EntAux.sum_toReal μ] at htot
  linarith
