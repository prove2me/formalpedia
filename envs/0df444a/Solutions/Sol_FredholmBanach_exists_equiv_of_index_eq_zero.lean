-- Prove2me | solution 1 for FredholmBanach.exists_equiv_of_index_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:00:38.676683+00:00
-- url     : https://prove2.me/submissions/09bf7c67-aace-424b-8d35-26e721598c1d

import Definitions.Def_FredholmBanach_Setting
import Mathlib.Analysis.Normed.Operator.Banach

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u : E →L[𝕜] F} (hu : u.IsFredholm) (h0 : FredholmBanach.index u = 0)
    (h : Function.Injective u ∨ Function.Surjective u) :
    ∃ e : E ≃L[𝕜] F, (e : E →L[𝕜] F) = u := by
  haveI : FiniteDimensional 𝕜 u.ker := hu.finite_ker
  haveI : FiniteDimensional 𝕜 (F ⧸ u.range) := hu.finite_coker
  have hrank : Module.finrank 𝕜 u.ker = Module.finrank 𝕜 (F ⧸ u.range) := by
    unfold FredholmBanach.index at h0
    omega
  have hker : u.ker = ⊥ ∧ u.range = ⊤ := by
    rcases h with hi | hs
    · have hk : u.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
      refine ⟨hk, ?_⟩
      have h1 : Module.finrank 𝕜 u.ker = 0 := by
        rw [Submodule.finrank_eq_zero]; exact hk
      rw [h1, eq_comm, Module.finrank_zero_iff] at hrank
      rw [eq_top_iff]
      intro y _
      have : (Submodule.mkQ u.range y) = 0 := Subsingleton.elim _ _
      simpa using this
    · have hr : u.range = ⊤ := LinearMap.range_eq_top.mpr hs
      refine ⟨?_, hr⟩
      have h1 : Module.finrank 𝕜 (F ⧸ u.range) = 0 := by
        rw [Module.finrank_zero_iff]
        refine ⟨fun a b => ?_⟩
        induction a using Submodule.Quotient.induction_on with | _ a => ?_
        induction b using Submodule.Quotient.induction_on with | _ b => ?_
        rw [Submodule.Quotient.eq, hr]; trivial
      rw [h1, Submodule.finrank_eq_zero] at hrank
      exact hrank
  exact ⟨ContinuousLinearEquiv.ofBijective u hker.1 hker.2, rfl⟩
