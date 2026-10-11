-- Prove2me | solution 1 for FredholmBanach.isFredholm_index_of_bijective_coprod
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:26:48.824988+00:00
-- url     : https://prove2.me/submissions/3c064fc1-9e52-4eea-b625-ef4ebf94b772

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isFredholm_iff_finiteDimensional
import Mathlib.Algebra.Module.LinearMap.Index

/-- If `(x, c) ↦ v x + c` is a bijection `E₀ × C → F`, with `E ⧸ E₀` and `C` finite-dimensional,
then `v` is Fredholm of index `dim (E ⧸ E₀) - dim C`. -/
theorem solution {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (E₀ : Submodule 𝕜 E) [FiniteDimensional 𝕜 (E ⧸ E₀)] (C : Submodule 𝕜 F) [FiniteDimensional 𝕜 C]
    (v : E →L[𝕜] F) (hv : Function.Bijective ((v.comp E₀.subtypeL).coprod C.subtypeL)) :
    v.IsFredholm ∧ FredholmBanach.index v =
      (Module.finrank 𝕜 (E ⧸ E₀) : ℤ) - (Module.finrank 𝕜 C : ℤ) := by
  set L : E →ₗ[𝕜] F := (v : E →ₗ[𝕜] F)
  set w : E₀ →ₗ[𝕜] F := L ∘ₗ E₀.subtype
  have hT : ∀ (x : E₀) (c : C), (v.comp E₀.subtypeL).coprod C.subtypeL (x, c) = w x + c :=
    fun _ _ => rfl
  have hinj : Function.Injective w := by
    intro x y h
    have := @hv.1 (x, 0) (y, 0) (by rw [hT, hT]; simpa using h)
    exact congrArg Prod.fst this
  have hcompl : IsCompl (LinearMap.range w) C := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro z ⟨x, rfl⟩ hz
      have := @hv.1 (x, -⟨w x, hz⟩) (0, 0) (by rw [hT, hT]; simp)
      have h2 := congrArg Prod.fst this
      simp only at h2
      rw [h2]; simp
    · rw [codisjoint_iff, eq_top_iff]
      intro y _
      obtain ⟨⟨x, c⟩, hxc⟩ := hv.2 y
      rw [hT] at hxc
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
