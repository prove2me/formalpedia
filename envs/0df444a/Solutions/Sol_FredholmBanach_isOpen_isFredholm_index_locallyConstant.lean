-- Prove2me | solution 1 for FredholmBanach.isOpen_isFredholm_index_locallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:20:35.560953+00:00
-- url     : https://prove2.me/submissions/8642ffd5-290b-442e-b961-c433aa4dfcfb

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isFredholm_iff_finiteDimensional
import Mathlib.Algebra.Module.LinearMap.Index
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
    have hv : Function.Bijective ((v.comp E₀.subtypeL).coprod C.subtypeL) := by
      change Function.Bijective (T v)
      rw [← he]; exact e.bijective
    set L : E →ₗ[𝕜] F := (v : E →ₗ[𝕜] F)
    set w : E₀ →ₗ[𝕜] F := L ∘ₗ E₀.subtype
    have hT' : ∀ (x : E₀) (c : C), (v.comp E₀.subtypeL).coprod C.subtypeL (x, c) = w x + c :=
      fun _ _ => rfl
    have hinj : Function.Injective w := by
      intro x y h
      have := @hv.1 (x, 0) (y, 0) (by rw [hT', hT']; simpa using h)
      exact congrArg Prod.fst this
    have hcompl : IsCompl (LinearMap.range w) C := by
      constructor
      · rw [Submodule.disjoint_def]
        rintro z ⟨x, rfl⟩ hz
        have := @hv.1 (x, -⟨w x, hz⟩) (0, 0) (by rw [hT', hT']; simp)
        have h2 := congrArg Prod.fst this
        simp only at h2
        rw [h2]; simp
      · rw [codisjoint_iff, eq_top_iff]
        intro y _
        obtain ⟨⟨x, c⟩, hxc⟩ := hv.2 y
        rw [hT'] at hxc
        rw [← hxc]
        exact Submodule.add_mem_sup ⟨x, rfl⟩ c.2
    let eq := Submodule.quotientEquivOfIsCompl _ _ hcompl
    haveI : FiniteDimensional 𝕜 (F ⧸ LinearMap.range w) := eq.symm.finiteDimensional
    have hkerv : FiniteDimensional 𝕜 (LinearMap.ker L) := by
      refine Module.Finite.of_injective (E₀.mkQ ∘ₗ (LinearMap.ker L).subtype) ?_
      intro a b hab
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Submodule.mkQ_apply, Submodule.Quotient.eq] at hab
      have h0 : w ⟨(a : E) - b, hab⟩ = w 0 := by
        simp [w, L, LinearMap.mem_ker.mp a.2, LinearMap.mem_ker.mp b.2]
      have := congrArg Subtype.val (hinj h0)
      simp only [ZeroMemClass.coe_zero] at this
      exact Subtype.ext (sub_eq_zero.mp this)
    have hcok : FiniteDimensional 𝕜 (F ⧸ LinearMap.range L) :=
      Module.Finite.of_surjective (Submodule.factor (LinearMap.range_comp_le_range E₀.subtype L))
        (Submodule.factor_surjective _)
    refine ⟨(FredholmBanach.isFredholm_iff_finiteDimensional v).mpr ⟨hkerv, hcok⟩, ?_⟩
    haveI := hkerv; haveI := hcok
    haveI : FiniteDimensional 𝕜 (LinearMap.ker E₀.subtype) := by
      rw [Submodule.ker_subtype]; infer_instance
    haveI : FiniteDimensional 𝕜 (E ⧸ LinearMap.range E₀.subtype) := by
      rw [Submodule.range_subtype]; infer_instance
    have e1 := LinearMap.index_comp (f := E₀.subtype) L
    have e2 := LinearMap.index_of_injective hinj
    have e3 := LinearMap.index_of_injective (R := 𝕜) E₀.injective_subtype
    rw [Submodule.range_subtype] at e3
    have e4 := eq.finrank_eq
    change L.index = _
    change w.index = _ at e1
    lia
  refine ⟨isOpen_iff_mem_nhds.mpr fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨n, h⟩ := key u hu
    exact h.mono fun v hv => hv.1
  · obtain ⟨n, h⟩ := key u hu
    have hu' := h.self_of_nhds.2
    exact h.mono fun v hv => hv.2.trans hu'.symm
