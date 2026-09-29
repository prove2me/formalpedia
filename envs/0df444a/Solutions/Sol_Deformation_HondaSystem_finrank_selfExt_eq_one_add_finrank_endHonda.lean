-- Prove2me | solution 1 for Deformation.HondaSystem.finrank_selfExt_eq_one_add_finrank_endHonda
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ee344059-67d0-54ea-82c5-e2acafdcb67b

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_finrank_selfExt_eq_one_add_finrank_endHonda

set_option autoImplicit false

open Module LinearMap Submodule Function

universe u v

namespace HondaSelfExtCount

variable {k : Type u} [Field k]

section Coordinates

def Em (Fm Vm : Matrix (Fin 2) (Fin 2) k) :
    Submodule k (Matrix (Fin 2) (Fin 2) k × Matrix (Fin 2) (Fin 2) k) :=
  LinearMap.ker
    ((((LinearMap.mulLeft k Fm).comp (LinearMap.snd k _ _)) +
        ((LinearMap.mulRight k Vm).comp (LinearMap.fst k _ _))).prod
      (((LinearMap.mulLeft k Vm).comp (LinearMap.fst k _ _)) +
        ((LinearMap.mulRight k Fm).comp (LinearMap.snd k _ _))))

theorem mem_Em_iff (Fm Vm : Matrix (Fin 2) (Fin 2) k)
    (p : Matrix (Fin 2) (Fin 2) k × Matrix (Fin 2) (Fin 2) k) :
    p ∈ Em Fm Vm ↔ Fm * p.2 + p.1 * Vm = 0 ∧ Vm * p.1 + p.2 * Fm = 0 := by
  simp [Em]

variable (α β γ δ : k)

def theta : (Fin 5 → k) →ₗ[k] Matrix (Fin 2) (Fin 2) k × Matrix (Fin 2) (Fin 2) k where
  toFun c := (!![c 1, c 2; c 0 * α, c 0 * β], !![-(γ * c 0), c 3; -(δ * c 0), c 4])
  map_add' c d := by
    refine Prod.ext ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' r c := by
    refine Prod.ext ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring

theorem theta_apply (c : Fin 5 → k) :
    theta α β γ δ c = (!![c 1, c 2; c 0 * α, c 0 * β], !![-(γ * c 0), c 3; -(δ * c 0), c 4]) :=
  rfl

def gfun : (Fin 5 → k) →ₗ[k] k :=
  α • LinearMap.proj 3 + β • LinearMap.proj 4 + γ • LinearMap.proj 1 + δ • LinearMap.proj 2

theorem gfun_apply (c : Fin 5 → k) :
    gfun α β γ δ c = α * c 3 + β * c 4 + γ * c 1 + δ * c 2 := by
  simp [gfun]

theorem theta_injective (hαβ : α ≠ 0 ∨ β ≠ 0) : Function.Injective (theta α β γ δ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  rw [theta_apply, Prod.mk_eq_zero] at hc
  obtain ⟨hX, hY⟩ := hc
  have h1 : c 1 = 0 := by simpa using congr_fun (congr_fun hX 0) 0
  have h2 : c 2 = 0 := by simpa using congr_fun (congr_fun hX 0) 1
  have h3 : c 3 = 0 := by simpa using congr_fun (congr_fun hY 0) 1
  have h4 : c 4 = 0 := by simpa using congr_fun (congr_fun hY 1) 1
  have h0a : c 0 * α = 0 := by simpa using congr_fun (congr_fun hX 1) 0
  have h0b : c 0 * β = 0 := by simpa using congr_fun (congr_fun hX 1) 1
  have h0 : c 0 = 0 := by
    rcases hαβ with hα | hβ
    · exact (mul_eq_zero.mp h0a).resolve_right hα
    · exact (mul_eq_zero.mp h0b).resolve_right hβ
  ext i
  fin_cases i <;> simp [h0, h1, h2, h3, h4]

theorem gfun_surjective (hαβ : α ≠ 0 ∨ β ≠ 0) : Function.Surjective (gfun α β γ δ) := by
  intro t
  rcases hαβ with hα | hβ
  · refine ⟨Pi.single 3 (t / α), ?_⟩
    rw [gfun_apply]
    simp
    field_simp
  · refine ⟨Pi.single 4 (t / β), ?_⟩
    rw [gfun_apply]
    simp
    field_simp

theorem finrank_ker_gfun (hαβ : α ≠ 0 ∨ β ≠ 0) :
    finrank k (LinearMap.ker (gfun α β γ δ)) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (gfun α β γ δ)
  rw [LinearMap.range_eq_top.mpr (gfun_surjective α β γ δ hαβ), finrank_top,
    Module.finrank_self, Module.finrank_fin_fun] at h
  omega

theorem map_theta_ker_le (rel : α * γ + β * δ = 0) :
    (LinearMap.ker (gfun α β γ δ)).map (theta α β γ δ) ≤
      Em !![α, β; 0, 0] !![0, γ; 0, δ] := by
  rintro _ ⟨c, hc, rfl⟩
  replace hc : α * c 3 + β * c 4 + γ * c 1 + δ * c 2 = 0 := by
    simpa [gfun_apply] using hc
  rw [mem_Em_iff, theta_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (-c 0) * rel
    · linear_combination hc
    · linear_combination (c 0) * rel
  · ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem le_map_theta_ker (rel : α * γ + β * δ = 0) (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hγδ : γ ≠ 0 ∨ δ ≠ 0) :
    Em !![α, β; 0, 0] !![0, γ; 0, δ] ≤
      (LinearMap.ker (gfun α β γ δ)).map (theta α β γ δ) := by
  rintro ⟨X, Y⟩ hXY
  rw [mem_Em_iff] at hXY
  obtain ⟨h1, h2⟩ := hXY

  have E1 : α * Y 0 0 + β * Y 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using congr_fun (congr_fun h1 0) 0
  have E2 : α * Y 0 1 + β * Y 1 1 + (X 0 0 * γ + X 0 1 * δ) = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using congr_fun (congr_fun h1 0) 1
  have E3 : X 1 0 * γ + X 1 1 * δ = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using congr_fun (congr_fun h1 1) 1
  have E4 : γ * X 1 0 + Y 0 0 * α = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using congr_fun (congr_fun h2 0) 0
  have E5 : γ * X 1 1 + Y 0 0 * β = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using congr_fun (congr_fun h2 0) 1
  have E6 : δ * X 1 0 + Y 1 0 * α = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using congr_fun (congr_fun h2 1) 0
  have E7 : δ * X 1 1 + Y 1 0 * β = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using congr_fun (congr_fun h2 1) 1

  have E8 : α * X 1 1 = β * X 1 0 := by
    have hd : δ * (α * X 1 1 - β * X 1 0) = 0 := by
      linear_combination α * E3 - (X 1 0) * rel
    have hg : γ * (α * X 1 1 - β * X 1 0) = 0 := by
      linear_combination (-β) * E3 + (X 1 1) * rel
    rcases hγδ with hγ | hδ
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hg).resolve_left hγ)
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hδ)
  rcases hαβ with hα | hβ
  ·
    refine ⟨![X 1 0 / α, X 0 0, X 0 1, Y 0 1, Y 1 1], ?_, ?_⟩
    · change _ ∈ LinearMap.ker (gfun α β γ δ)
      rw [LinearMap.mem_ker, gfun_apply]
      simp only [Matrix.cons_val]
      linear_combination E2
    · rw [theta_apply]
      refine Prod.ext ?_ ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp
        · field_simp
        · field_simp
          linear_combination -E8
      · ext i j
        fin_cases i <;> fin_cases j <;> simp
        · field_simp
          linear_combination -E4
        · field_simp
          linear_combination -E6
  ·
    refine ⟨![X 1 1 / β, X 0 0, X 0 1, Y 0 1, Y 1 1], ?_, ?_⟩
    · change _ ∈ LinearMap.ker (gfun α β γ δ)
      rw [LinearMap.mem_ker, gfun_apply]
      simp only [Matrix.cons_val]
      linear_combination E2
    · rw [theta_apply]
      refine Prod.ext ?_ ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp
        · field_simp
          linear_combination E8
        · field_simp
      · ext i j
        fin_cases i <;> fin_cases j <;> simp
        · field_simp
          linear_combination -E5
        · field_simp
          linear_combination -E7

theorem finrank_Em (rel : α * γ + β * δ = 0) (hαβ : α ≠ 0 ∨ β ≠ 0) (hγδ : γ ≠ 0 ∨ δ ≠ 0) :
    finrank k (Em !![α, β; 0, 0] !![0, γ; 0, δ]) = 4 := by
  have hEq : Em !![α, β; 0, 0] !![0, γ; 0, δ] =
      (LinearMap.ker (gfun α β γ δ)).map (theta α β γ δ) :=
    le_antisymm (le_map_theta_ker α β γ δ rel hαβ hγδ) (map_theta_ker_le α β γ δ rel)
  rw [hEq, ← finrank_ker_gfun α β γ δ hαβ]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (theta_injective α β γ δ hαβ) _)).symm

end Coordinates

section Honda

variable {D : Type v} [AddCommGroup D] [Module k D] [FiniteDimensional k D]
  {ℓ : k} (H : Deformation.HondaSystem ℓ D)

omit [FiniteDimensional k D] in

theorem range_inf_L_eq_bot (hℓ : ℓ = 0) : LinearMap.range H.F ⊓ H.L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, -, hxy⟩ := H.sh1_le x hx.2 hx.1
  rw [Submodule.mem_bot, hxy, hℓ, zero_smul]

theorem finrank_range_F (hℓ : ℓ = 0) (hD : finrank k D = 2) (hL : finrank k H.L = 1) :
    finrank k (LinearMap.range H.F) = 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range H.F) H.L
  rw [H.sh2', range_inf_L_eq_bot H hℓ, finrank_top, finrank_bot, hD, hL] at h
  omega

theorem exists_adapted_basis (hℓ : ℓ = 0) (hD : finrank k D = 2) (hL : finrank k H.L = 1) :
    ∃ (b : Basis (Fin 2) k D) (α β γ δ : k),
      b 1 ∈ H.L ∧ (∀ x ∈ H.L, ∃ c : k, c • b 1 = x) ∧
      H.F (b 0) = α • b 0 ∧ H.F (b 1) = β • b 0 ∧ H.V (b 0) = 0 ∧
      H.V (b 1) = γ • b 0 + δ • b 1 ∧
      α * γ + β * δ = 0 ∧ (α ≠ 0 ∨ β ≠ 0) ∧ (γ ≠ 0 ∨ δ ≠ 0) := by

  have hR1 := finrank_range_F H hℓ hD hL
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hR1
  obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp hL
  set e₁ : D := (v : D) with he₁
  set e₂ : D := (w : D) with he₂
  have he₁0 : e₁ ≠ 0 := fun h => hv0 (Subtype.ext h)
  have he₂0 : e₂ ≠ 0 := fun h => hw0 (Subtype.ext h)
  have he₁mem : e₁ ∈ LinearMap.range H.F := v.2
  have he₂mem : e₂ ∈ H.L := w.2
  have hgen₁ : ∀ x ∈ LinearMap.range H.F, ∃ c : k, c • e₁ = x := by
    intro x hx
    obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
    exact ⟨c, by simpa [he₁] using congr_arg Subtype.val hc⟩
  have hgen₂ : ∀ x ∈ H.L, ∃ c : k, c • e₂ = x := by
    intro x hx
    obtain ⟨c, hc⟩ := hw ⟨x, hx⟩
    exact ⟨c, by simpa [he₂] using congr_arg Subtype.val hc⟩

  have hli : LinearIndependent k ![e₁, e₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hs1 : s • e₁ ∈ LinearMap.range H.F ⊓ H.L := by
      refine ⟨Submodule.smul_mem _ _ he₁mem, ?_⟩
      have : s • e₁ = -(t • e₂) := eq_neg_of_add_eq_zero_left hst
      rw [this]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ he₂mem)
    rw [range_inf_L_eq_bot H hℓ, Submodule.mem_bot] at hs1
    have hs : s = 0 := (smul_eq_zero.mp hs1).resolve_right he₁0
    rw [hs, zero_smul, zero_add] at hst
    exact ⟨hs, (smul_eq_zero.mp hst).resolve_right he₂0⟩
  let b : Basis (Fin 2) k D := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hD])
  have hb0 : b 0 = e₁ := by simp [b]
  have hb1 : b 1 = e₂ := by simp [b]

  obtain ⟨α, hα⟩ := hgen₁ (H.F e₁) (LinearMap.mem_range_self _ _)
  obtain ⟨β, hβ⟩ := hgen₁ (H.F e₂) (LinearMap.mem_range_self _ _)
  have hVe₁ : H.V e₁ = 0 := by
    obtain ⟨d, hd⟩ := he₁mem
    rw [← hd, H.toDieudonneDatum.V_F_apply, hℓ, zero_smul]
  set γ : k := b.repr (H.V e₂) 0 with hγ
  set δ : k := b.repr (H.V e₂) 1 with hδ
  have hVe₂ : H.V e₂ = γ • e₁ + δ • e₂ := by
    have h := b.sum_repr (H.V e₂)
    rw [Fin.sum_univ_two, hb0, hb1] at h
    exact h.symm

  have rel : α * γ + β * δ = 0 := by
    have h : H.F (H.V e₂) = 0 := by
      rw [H.toDieudonneDatum.F_V_apply, hℓ, zero_smul]
    rw [hVe₂, map_add, map_smul, map_smul, ← hα, ← hβ, smul_smul, smul_smul, ← add_smul,
      smul_eq_zero] at h
    rcases h with h | h
    · linear_combination h
    · exact absurd h he₁0

  have hαβ : α ≠ 0 ∨ β ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hα0, hβ0⟩ := hcon
    have hF0 : H.F = 0 := by
      refine b.ext fun i => ?_
      fin_cases i
      · simp [hb0, ← hα, hα0]
      · simp [hb1, ← hβ, hβ0]
    have : finrank k (LinearMap.range H.F) = 0 := by
      rw [hF0, LinearMap.range_zero, finrank_bot]
    omega

  have hγδ : γ ≠ 0 ∨ δ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hγ0, hδ0⟩ := hcon
    have hV0 : H.V e₂ = 0 := by rw [hVe₂, hγ0, hδ0, zero_smul, zero_smul, add_zero]
    exact he₂0 (H.sh3 e₂ he₂mem hV0)
  refine ⟨b, α, β, γ, δ, ?_, ?_, ?_, ?_, ?_, ?_, rel, hαβ, hγδ⟩
  · rw [hb1]; exact he₂mem
  · intro x hx; rw [hb1]; exact hgen₂ x hx
  · rw [hb0]; exact hα.symm
  · rw [hb1, hb0]; exact hβ.symm
  · rw [hb0]; exact hVe₁
  · rw [hb1, hb0]; exact hVe₂

omit [FiniteDimensional k D] in

theorem toMatrix_F_eq (b : Basis (Fin 2) k D) (α β : k)
    (hF0 : H.F (b 0) = α • b 0) (hF1 : H.F (b 1) = β • b 0) :
    LinearMap.toMatrix b b H.F = !![α, β; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, hF0, hF1]

omit [FiniteDimensional k D] in
theorem toMatrix_V_eq (b : Basis (Fin 2) k D) (γ δ : k)
    (hV0 : H.V (b 0) = 0) (hV1 : H.V (b 1) = γ • b 0 + δ • b 1) :
    LinearMap.toMatrix b b H.V = !![0, γ; 0, δ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, hV0, hV1]

theorem finrank_extPairs (hℓ : ℓ = 0) (hD : finrank k D = 2) (hL : finrank k H.L = 1) :
    finrank k H.extPairs = 4 := by
  classical
  obtain ⟨b, α, β, γ, δ, -, -, hF0, hF1, hV0, hV1, rel, hαβ, hγδ⟩ :=
    exists_adapted_basis H hℓ hD hL
  set Φ : Module.End k D ≃ₗ[k] Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b with hΦ
  have hFm : Φ H.F = !![α, β; 0, 0] := toMatrix_F_eq H b α β hF0 hF1
  have hVm : Φ H.V = !![0, γ; 0, δ] := toMatrix_V_eq H b γ δ hV0 hV1
  set e : (Module.End k D × Module.End k D) ≃ₗ[k]
      (Matrix (Fin 2) (Fin 2) k × Matrix (Fin 2) (Fin 2) k) := Φ.prodCongr Φ with he
  have hcomap : H.extPairs = (Em !![α, β; 0, 0] !![0, γ; 0, δ]).comap e.toLinearMap := by
    ext ⟨X, Y⟩
    rw [Submodule.mem_comap, Deformation.HondaSystem.mem_extPairs_iff, LinearEquiv.coe_coe,
      mem_Em_iff]
    have h1 : (e (X, Y)).1 = Φ X := rfl
    have h2 : (e (X, Y)).2 = Φ Y := rfl
    rw [h1, h2, ← hFm, ← hVm]
    simp only [hΦ, ← LinearMap.toMatrix_comp b b b, ← map_add]
    rw [(LinearMap.toMatrix b b).map_eq_zero_iff, (LinearMap.toMatrix b b).map_eq_zero_iff]
  rw [hcomap, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  exact finrank_Em α β γ δ rel hαβ hγδ

theorem finrank_end (hD : finrank k D = 2) : finrank k (Module.End k D) = 4 := by
  rw [Module.finrank_linearMap, hD]

theorem finrank_filteredEnd (hℓ : ℓ = 0) (hD : finrank k D = 2) (hL : finrank k H.L = 1) :
    finrank k H.filteredEnd = 3 := by
  obtain ⟨b, α, β, γ, δ, hb1, hgen, -, -, -, -, -, -, -⟩ := exists_adapted_basis H hℓ hD hL

  let ψ : Module.End k D →ₗ[k] D ⧸ H.L := H.L.mkQ ∘ₗ LinearMap.applyₗ (b 1)
  have hψ : ∀ a : Module.End k D, ψ a = H.L.mkQ (a (b 1)) := fun a => rfl
  have hker : LinearMap.ker ψ = H.filteredEnd := by
    ext a
    rw [LinearMap.mem_ker, hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Deformation.HondaSystem.mem_filteredEnd_iff]
    constructor
    · intro ha x hx
      obtain ⟨c, rfl⟩ := hgen x hx
      rw [map_smul]
      exact Submodule.smul_mem _ _ ha
    · intro ha
      exact ha _ hb1
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective H.L q
    refine ⟨(b.coord 1).smulRight d, ?_⟩
    rw [hψ, LinearMap.smulRight_apply, Basis.coord_apply, b.repr_self, Finsupp.single_eq_same,
      one_smul]
  have hq : finrank k (D ⧸ H.L) = 1 := by
    have h := H.L.finrank_quotient_add_finrank
    rw [hD, hL] at h
    omega
  have h := LinearMap.finrank_range_add_finrank_ker ψ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hq, hker, finrank_end hD] at h
  omega

theorem finrank_innerPairs_add (hℓ : ℓ = 0) (hD : finrank k D = 2) (hL : finrank k H.L = 1) :
    finrank k H.innerPairs + finrank k H.endHonda = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (H.innerDerivation.domRestrict H.filteredEnd)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, finrank_filteredEnd H hℓ hD hL] at h
  have hk : finrank k (Submodule.comap H.filteredEnd.subtype (LinearMap.ker H.innerDerivation)) =
      finrank k H.endHonda := by
    have hc : Submodule.comap H.filteredEnd.subtype (LinearMap.ker H.innerDerivation) =
        Submodule.comap H.filteredEnd.subtype
          (H.filteredEnd ⊓ LinearMap.ker H.innerDerivation) := by
      rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
    rw [hc]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)
  rw [hk] at h
  exact h

theorem finrank_selfExt (hℓ : ℓ = 0) (hD : finrank k D = 2) (hL : finrank k H.L = 1) :
    finrank k H.selfExt = 1 + finrank k H.endHonda := by
  have hE := finrank_extPairs H hℓ hD hL
  have hC := finrank_innerPairs_add H hℓ hD hL
  have hle : H.innerPairs ≤ H.extPairs := H.innerPairs_le_extPairs
  have hq := (H.innerPairs.comap H.extPairs.subtype).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle), hE] at hq
  change finrank k (↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)) = _
  omega

end Honda

end HondaSelfExtCount

theorem solution {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D]
    [FiniteDimensional k D] {ℓ : k} (hℓ : ℓ = 0) (H : Deformation.HondaSystem ℓ D)
    (hD : Module.finrank k D = 2) (hL : Module.finrank k H.L = 1) :
    Module.finrank k H.selfExt = 1 + Module.finrank k H.endHonda :=
  HondaSelfExtCount.finrank_selfExt H hℓ hD hL

end S_Deformation_HondaSystem_finrank_selfExt_eq_one_add_finrank_endHonda
end P2MW
export P2MW.S_Deformation_HondaSystem_finrank_selfExt_eq_one_add_finrank_endHonda (solution)
