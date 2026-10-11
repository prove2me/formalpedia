-- Prove2me | solution 1 for FredholmBanach.compact_perturbation_coker
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:13:39.110984+00:00
-- url     : https://prove2.me/submissions/fc889334-0467-4673-b388-e608f3742645

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isClosed_range_of_finiteDimensional_coker
import Theorems.Thm_FredholmBanach_surjective_of_approx_preimage
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u h : E →L[𝕜] F} (hc : FiniteDimensional 𝕜 (F ⧸ u.range)) (hh : IsCompactOperator h) :
    FiniteDimensional 𝕜 (F ⧸ (u + h).range) ∧ IsClosed ((u + h).range : Set F) := by
  -- a finite-dimensional algebraic complement `C` of `range u`
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl u.range
  haveI : FiniteDimensional 𝕜 C := (Submodule.quotientEquivOfIsCompl _ _ hC).finiteDimensional
  haveI : CompleteSpace C := FiniteDimensional.complete 𝕜 C
  -- `Ψ (x, c) = u x + c` is onto, hence has preimages with norm control
  let Ψ : (E × C) →L[𝕜] F := u.coprod C.subtypeL
  have hΨ : Function.Surjective Ψ := by
    intro y
    have hy : y ∈ u.range ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨x, rfl⟩ := ha
    exact ⟨(x, ⟨c, hc'⟩), rfl⟩
  obtain ⟨A, hA0, hA⟩ := Ψ.exists_preimage_norm_le hΨ
  -- a finite `1/2`-net `t` of the compact set `K`
  have hK : IsCompact (closure (h '' Metric.closedBall 0 A)) :=
    hh.isCompact_closure_image_closedBall A
  obtain ⟨t, htK, ht, hcov⟩ := finite_cover_balls_of_compact hK (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set M : Submodule 𝕜 F := C ⊔ Submodule.span 𝕜 t with hM
  haveI : FiniteDimensional 𝕜 (Submodule.span 𝕜 t) := FiniteDimensional.span_of_finite 𝕜 ht
  haveI : FiniteDimensional 𝕜 M := Submodule.finiteDimensional_sup _ _
  haveI : CompleteSpace M := FiniteDimensional.complete 𝕜 M
  -- `Φ (x, m) = (u + h) x + m` is onto
  let Φ : (E × M) →L[𝕜] F := (u + h).coprod M.subtypeL
  have hΦ : Function.Surjective Φ := by
    refine FredholmBanach.surjective_of_approx_preimage Φ (C := A + max R 0) fun y hy => ?_
    obtain ⟨⟨x, c⟩, hxc, hn⟩ := hA y
    have hxc' : u x + (c : F) = y := hxc
    have hn' : ‖((x, c) : E × C)‖ ≤ A := by
      calc _ ≤ A * ‖y‖ := hn
        _ ≤ A * 1 := by gcongr
        _ = A := mul_one A
    have hx : ‖x‖ ≤ A := (norm_fst_le _).trans hn'
    have hcn : ‖(c : F)‖ ≤ A := (norm_snd_le ((x, c) : E × C)).trans hn'
    have hxK : h x ∈ closure (h '' Metric.closedBall 0 A) :=
      subset_closure ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hcov hxK)
    have hiM : (c : F) - i ∈ M :=
      M.sub_mem (Submodule.mem_sup_left c.2)
        (Submodule.mem_sup_right (Submodule.subset_span hi))
    refine ⟨(x, ⟨(c : F) - i, hiM⟩), ?_, ?_⟩
    · refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
      · have := le_max_right R 0
        dsimp only
        linarith
      · show ‖(c : F) - i‖ ≤ A + max R 0
        have := hR i (htK hi)
        have := le_max_left R 0
        calc ‖(c : F) - i‖ ≤ ‖(c : F)‖ + ‖i‖ := norm_sub_le _ _
          _ ≤ A + max R 0 := by linarith
    · have : Φ (x, ⟨(c : F) - i, hiM⟩) - y = h x - i := by
        show (u + h) x + ((c : F) - i) - y = h x - i
        rw [← hxc', ContinuousLinearMap.add_apply]
        abel
      rw [this, ← dist_eq_norm]
      exact (Metric.mem_ball.mp hxi).le
  have htop : (u + h).range ⊔ M = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨⟨x, m⟩, rfl⟩ := hΦ y
    exact Submodule.add_mem_sup ⟨x, rfl⟩ m.2
  haveI hfin : Module.Finite 𝕜 (F ⧸ (u + h).range) := by
    rw [Module.finite_def, ← (Submodule.map_mkQ_eq_top _ _).mpr htop]
    exact (Module.Finite.iff_fg.mp inferInstance : M.FG).map _
  exact ⟨hfin, (FredholmBanach.isClosed_range_of_finiteDimensional_coker (u + h) hfin).1⟩
