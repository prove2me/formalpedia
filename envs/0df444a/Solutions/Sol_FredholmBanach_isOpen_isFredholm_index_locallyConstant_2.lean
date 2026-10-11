-- Prove2me | solution 2 for FredholmBanach.isOpen_isFredholm_index_locallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:32:49.974445+00:00
-- url     : https://prove2.me/submissions/9aad4170-66a0-4414-a1bc-5a0c81c892fa

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isFredholm_index_of_bijective_coprod
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Banach

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] :
    IsOpen {u : E →L[𝕜] F | u.IsFredholm} ∧
      ∀ u : E →L[𝕜] F, u.IsFredholm →
        ∀ᶠ v in 𝓝 u, FredholmBanach.index v = FredholmBanach.index u := by
  have key : ∀ u : E →L[𝕜] F, u.IsFredholm →
      ∃ n : ℤ, ∀ᶠ v in 𝓝 u, v.IsFredholm ∧ FredholmBanach.index v = n := by
    intro u hu
    obtain ⟨E₀, hE₀c, hE₀⟩ := hu.closedComplemented_ker.exists_isClosed_isCompl
    haveI : FiniteDimensional 𝕜 u.ker := hu.finite_ker
    haveI : FiniteDimensional 𝕜 (F ⧸ u.range) := hu.finite_coker
    haveI : FiniteDimensional 𝕜 (E ⧸ E₀) :=
      (Submodule.quotientEquivOfIsCompl E₀ _ hE₀.symm).symm.finiteDimensional
    obtain ⟨C, hC⟩ := (u.range : Submodule 𝕜 F).exists_isCompl
    haveI : FiniteDimensional 𝕜 C := (Submodule.quotientEquivOfIsCompl _ _ hC).finiteDimensional
    haveI : CompleteSpace E₀ := hE₀c.completeSpace_coe
    haveI : CompleteSpace C := FiniteDimensional.complete 𝕜 C
    let T : (E →L[𝕜] F) → (E₀ × C →L[𝕜] F) := fun v => (v.comp E₀.subtypeL).coprod C.subtypeL
    have hTeq : T = fun v => v.comp (E₀.subtypeL.comp (ContinuousLinearMap.fst 𝕜 E₀ C)) +
        C.subtypeL.comp (ContinuousLinearMap.snd 𝕜 E₀ C) := by
      funext v; ext x <;> rfl
    have hTc : Continuous T := by
      rw [hTeq]; exact (continuous_id.clm_comp continuous_const).add continuous_const
    have hT : ∀ v : E →L[𝕜] F, ∀ (x : E₀) (c : C), T v (x, c) = v x + c := fun _ _ _ => rfl
    have hTu : Function.Bijective (T u) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        rintro ⟨x, c⟩ h
        rw [hT] at h
        have hc : (c : F) = 0 := by
          have hmem : (c : F) ∈ u.range ⊓ C :=
            ⟨⟨-(x : E), by simp [eq_neg_of_add_eq_zero_right h]⟩, c.2⟩
          rw [hC.inf_eq_bot] at hmem
          exact hmem
        rw [hc, add_zero] at h
        have hx : (x : E) ∈ u.ker ⊓ E₀ := ⟨h, x.2⟩
        rw [hE₀.inf_eq_bot, Submodule.mem_bot] at hx
        ext <;> simp [hx, hc]
      · intro y
        have hy : y ∈ u.range ⊔ C := by rw [hC.sup_eq_top]; trivial
        obtain ⟨a, ⟨e, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hy
        have he : e ∈ u.ker ⊔ E₀ := by rw [hE₀.sup_eq_top]; trivial
        obtain ⟨n, hn, x, hx, rfl⟩ := Submodule.mem_sup.mp he
        refine ⟨(⟨x, hx⟩, ⟨c, hc⟩), ?_⟩
        have hn' : u n = 0 := hn
        rw [hT]
        simp [hn']
    let e0 := ContinuousLinearEquiv.ofBijective (T u) (LinearMap.ker_eq_bot.mpr hTu.1)
      (LinearMap.range_eq_top.mpr hTu.2)
    have hnhds : ∀ᶠ v in 𝓝 u, T v ∈ Set.range (fun e : (E₀ × C) ≃L[𝕜] F => (e : (E₀ × C) →L[𝕜] F)) := by
      have := ContinuousLinearEquiv.nhds e0
      rw [ContinuousLinearEquiv.coe_ofBijective] at this
      exact hTc.continuousAt.preimage_mem_nhds this
    refine ⟨(Module.finrank 𝕜 (E ⧸ E₀) : ℤ) - (Module.finrank 𝕜 C : ℤ), hnhds.mono fun v hv => ?_⟩
    obtain ⟨e, he⟩ := hv
    refine FredholmBanach.isFredholm_index_of_bijective_coprod E₀ C v ?_
    change Function.Bijective (T v)
    rw [← he]; exact e.bijective
  refine ⟨isOpen_iff_mem_nhds.mpr fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨n, h⟩ := key u hu
    exact h.mono fun v hv => hv.1
  · obtain ⟨n, h⟩ := key u hu
    have hu' := h.self_of_nhds.2
    exact h.mono fun v hv => hv.2.trans hu'.symm
