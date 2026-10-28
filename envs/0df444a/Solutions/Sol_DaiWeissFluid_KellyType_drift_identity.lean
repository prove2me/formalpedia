-- Prove2me | solution 1 for DaiWeissFluid.KellyType.drift_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:23:33.952767+00:00
-- url     : https://prove2.me/submissions/6b047dea-239d-4b58-8a03-8d8f334ba1f2

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_KellyType_KellyLine

namespace Aux_Kelly_drift
open DaiWeissFluid.KellyType

lemma telescope {I K : ℕ} (L : ReentrantLine I K) (Q T : ℝ → Fin K → ℝ)
    (hsol : L.IsFluidSolution Q T) (s : ℝ) (hs : 0 ≤ s) :
    ∀ (j : ℕ) (hj : j < K),
      ∑ l ∈ Finset.univ.filter (· ≤ (⟨j, hj⟩ : Fin K)), (Q s l - Q 0 l) =
        s - L.μ ⟨j, hj⟩ * T s ⟨j, hj⟩ := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hfil : Finset.univ.filter (· ≤ (⟨0, hj⟩ : Fin K)) = {⟨0, hj⟩} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    rw [hfil, Finset.sum_singleton, hsol.flow s hs]
    unfold ReentrantLine.inflow
    rw [dif_pos rfl]
    ring
  | succ j ih =>
    intro hj
    have hj' : j < K := by omega
    have hfil : Finset.univ.filter (· ≤ (⟨j + 1, hj⟩ : Fin K)) =
        insert ⟨j + 1, hj⟩ (Finset.univ.filter (· ≤ (⟨j, hj'⟩ : Fin K))) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hnot : (⟨j + 1, hj⟩ : Fin K) ∉ Finset.univ.filter (· ≤ (⟨j, hj'⟩ : Fin K)) := by
      simp [Fin.le_iff_val_le_val]
    rw [hfil, Finset.sum_insert hnot, ih hj', hsol.flow s hs]
    unfold ReentrantLine.inflow
    rw [dif_neg (by simp)]
    have e : (⟨(j + 1) - 1, by omega⟩ : Fin K) = ⟨j, hj'⟩ := Fin.ext (by simp)
    simp only [e]
    ring

end Aux_Kelly_drift

open DaiWeissFluid.KellyType in
theorem solution {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (β : Fin I → ℝ) (hkelly : L.IsKellyType β)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T) (i : Fin I) (t : ℝ) (ht : 0 ≤ t) :
    L.kellyG Q i t = L.kellyG Q i 0 + ((L.C i).card : ℝ) * t - L.busy T i t / β i := by
  have hQp : ∀ k : Fin K, DaiWeissFluid.ThreeBuffer.Qplus Q k t =
      DaiWeissFluid.ThreeBuffer.Qplus Q k 0 + t - L.μ k * T t k := by
    intro k
    have := Aux_Kelly_drift.telescope L Q T hsol t ht k.val k.isLt
    simp only [Fin.eta] at this
    unfold DaiWeissFluid.ThreeBuffer.Qplus
    rw [Finset.sum_sub_distrib] at this
    linarith
  have hmu : ∀ k ∈ L.C i, L.μ k = (β i)⁻¹ := by
    intro k hk
    unfold ReentrantLine.μ
    rw [hkelly k]
    have : L.σ k = i := (Finset.mem_filter.mp hk).2
    rw [this]
  unfold ReentrantLine.kellyG ReentrantLine.busy
  have hsum : ∑ k ∈ L.C i, L.μ k * T t k = (β i)⁻¹ * ∑ k ∈ L.C i, T t k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k hk => by rw [hmu k hk])
  rw [Finset.sum_congr rfl (fun k _ => hQp k), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, hsum, div_eq_inv_mul]
