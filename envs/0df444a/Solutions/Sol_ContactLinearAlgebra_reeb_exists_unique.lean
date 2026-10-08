-- Prove2me | solution 1 for ContactLinearAlgebra.reeb_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T14:29:33.751184+00:00
-- url     : https://prove2.me/submissions/5659783f-2098-413f-9e73-f00f294ab486

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (a : V →ₗ[ℝ] ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hb : ∀ v, b v v = 0) (ha : ∃ v, a v ≠ 0)
    (hn : ∀ u, a u = 0 → (∀ v, a v = 0 → b u v = 0) → u = 0) :
    ∃! R : V, a R = 1 ∧ ∀ v, b R v = 0 := by
  classical
  let A : (V × ℝ) →ₗ[ℝ] Module.Dual ℝ (V × ℝ) :=
    { toFun := fun p =>
        { toFun := fun q => b p.1 q.1 + p.2 * a q.1 - q.2 * a p.1
          map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
          map_smul' := by
            intro s q
            change b p.1 (s • q.1) + p.2 * a (s • q.1) - (s * q.2) * a p.1 =
              s * (b p.1 q.1 + p.2 * a q.1 - q.2 * a p.1)
            simp only [map_smul, smul_eq_mul]; ring }
      map_add' := by
        intro p r
        apply LinearMap.ext
        intro q
        change b (p.1 + r.1) q.1 + (p.2 + r.2) * a q.1 - q.2 * a (p.1 + r.1) =
          (b p.1 q.1 + p.2 * a q.1 - q.2 * a p.1) +
          (b r.1 q.1 + r.2 * a q.1 - q.2 * a r.1)
        simp only [map_add, LinearMap.add_apply]; ring
      map_smul' := by
        intro s p
        apply LinearMap.ext
        intro q
        change b (s • p.1) q.1 + (s * p.2) * a q.1 - q.2 * a (s • p.1) =
          s * (b p.1 q.1 + p.2 * a q.1 - q.2 * a p.1)
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring }
  have hker : ∀ p, A p = 0 → p = 0 := by
    intro p hp
    have he (q : V × ℝ) : b p.1 q.1 + p.2 * a q.1 - q.2 * a p.1 = 0 :=
      congrArg (fun f : Module.Dual ℝ (V × ℝ) => f q) hp
    have hap : a p.1 = 0 := by
      have := he (0, 1)
      simpa using this
    have hu : p.1 = 0 := hn p.1 hap (by
      intro v hv
      have := he (v, 0)
      simpa [hv] using this)
    obtain ⟨v, hv⟩ := ha
    have hs : p.2 = 0 := by
      have hh := he (v, 0)
      simp [hu] at hh
      exact hh.resolve_right hv
    exact Prod.ext hu hs
  have hi : Function.Injective A := (LinearMap.ker_eq_bot).mp
    (by ext p; simp only [LinearMap.mem_ker, Submodule.mem_bot]; exact ⟨hker p, by rintro rfl; exact map_zero A⟩)
  have hs : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := V × ℝ)).symm).mp hi
  obtain ⟨p, hp⟩ := hs (-LinearMap.snd ℝ V ℝ)
  have he (q : V × ℝ) : b p.1 q.1 + p.2 * a q.1 - q.2 * a p.1 = -q.2 :=
    congrArg (fun f : Module.Dual ℝ (V × ℝ) => f q) hp
  have hap : a p.1 = 1 := by
    have := he (0, 1)
    simp only [map_zero, mul_zero, zero_add, one_mul, zero_sub] at this
    linarith
  have hsp : p.2 = 0 := by
    have := he (p.1, 0)
    simpa [hb, hap] using this
  have hbp (v : V) : b p.1 v = 0 := by simpa [hsp] using he (v, 0)
  refine ⟨p.1, ⟨hap, hbp⟩, ?_⟩
  intro R hR
  apply sub_eq_zero.mp
  apply hn (R - p.1)
  · simp [hR.1, hap]
  · intro v hv
    simp [map_sub, hR.2, hbp]
