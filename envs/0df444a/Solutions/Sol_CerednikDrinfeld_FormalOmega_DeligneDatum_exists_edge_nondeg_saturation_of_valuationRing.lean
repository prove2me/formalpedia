-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_edge_nondeg_saturation_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ec47f970-391d-57b5-b279-4be94135819c

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
import Theorems.Thm_LT_LatticeTree_FullLattice_eq_of_forall_smul_mem_of_le_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_edge_nondeg_saturation_of_valuationRing

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace V4Aux

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {V : Type} [CommRing V] [Algebra 𝒪 V]

def KI (M : FullLattice 𝒪 K) (φ : latticeBaseChange 𝒪 K V M →ₗ[V] V) (I : Ideal V) : Submodule 𝒪 (Fin 2 → K) where
  carrier := {w | ∃ h : w ∈ M.1, φ ((1 : V) ⊗ₜ[𝒪] (⟨w, h⟩ : ↥M.1)) ∈ I}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.1.add_mem ha hb, ?_⟩
    have : (⟨a + b, M.1.add_mem ha hb⟩ : ↥M.1) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [this, TensorProduct.tmul_add, map_add]; exact I.add_mem ha' hb'
  zero_mem' := ⟨M.1.zero_mem, by
    rw [show (⟨0, M.1.zero_mem⟩ : ↥M.1) = 0 from rfl, TensorProduct.tmul_zero, map_zero]; exact I.zero_mem⟩
  smul_mem' := by
    rintro r a ⟨ha, ha'⟩
    refine ⟨M.1.smul_mem r ha, ?_⟩
    have : (⟨r • a, M.1.smul_mem r ha⟩ : ↥M.1) = r • ⟨a, ha⟩ := rfl
    rw [this, TensorProduct.tmul_smul, ← algebraMap_smul V r, LinearMap.map_smul, smul_eq_mul]
    exact I.mul_mem_left _ ha'

theorem mem_KI (M : FullLattice 𝒪 K) (φ : latticeBaseChange 𝒪 K V M →ₗ[V] V) (I : Ideal V) (v : ↥M.1) :
    (v : Fin 2 → K) ∈ KI M φ I ↔ φ ((1 : V) ⊗ₜ[𝒪] v) ∈ I :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.2, h⟩⟩

theorem KI_le (M : FullLattice 𝒪 K) (φ : latticeBaseChange 𝒪 K V M →ₗ[V] V) (I : Ideal V) : KI M φ I ≤ M.1 :=
  fun _ ⟨h, _⟩ => h

def PiLat (πK : K) (M : FullLattice 𝒪 K) : Submodule 𝒪 (Fin 2 → K) where
  carrier := {v | ∃ w : ↥M.1, v = πK • (w : Fin 2 → K)}
  add_mem' := by
    rintro a b ⟨wa, rfl⟩ ⟨wb, rfl⟩
    exact ⟨wa + wb, by rw [Submodule.coe_add, smul_add]⟩
  zero_mem' := ⟨0, by rw [Submodule.coe_zero, smul_zero]⟩
  smul_mem' := by
    rintro r a ⟨w, rfl⟩
    exact ⟨r • w, by rw [Submodule.coe_smul, smul_comm]⟩

theorem mem_PiLat (πK : K) (M : FullLattice 𝒪 K) (v : Fin 2 → K) :
    v ∈ PiLat πK M ↔ ∃ w : ↥M.1, v = πK • (w : Fin 2 → K) := Iff.rfl

end V4Aux

open V4Aux in
set_option maxHeartbeats 4000000 in
theorem V4_main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V] (hV : algebraMap 𝒪 V π = 0)
    (L : Type) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (d : DeligneDatum (K := K) π L) (𝔭 : Ideal V) (h𝔭 : 𝔭.IsPrime) :
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : V) ⊗ₜ[𝒪] v ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M |
            LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M}
          ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : V) ⊗ₜ[𝒪] v' ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M' |
            LinearMap.rTensor (↥M'.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M'}
          ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M'))) := by
  classical
  let f : V →ₐ[𝒪] L := IsScalarTower.toAlgHom 𝒪 V L
  let πK : K := algebraMap 𝒪 K π

  let N₀ : ∀ M : FullLattice 𝒪 K, Submodule V (latticeBaseChange 𝒪 K V M) := fun M =>
    Submodule.span V {x : latticeBaseChange 𝒪 K V M | LinearMap.rTensor (↥M.1) f.toLinearMap x ∈ d.line M}
  have hmemN₀ : ∀ (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K V M),
      x ∈ N₀ M ↔ LinearMap.rTensor (↥M.1) f.toLinearMap x ∈ d.line M := by
    intro M x
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => rw [map_zero]; exact (d.line M).zero_mem
      | add y z _ _ hy hz => rw [map_add]; exact (d.line M).add_mem hy hz
      | smul a y _ hy =>
        rw [rTensor_smul_left f M a y]
        exact (d.line M).smul_mem (f a) hy
    · intro hx; exact Submodule.subset_span hx
  have hfin : ∀ M : FullLattice 𝒪 K, Module.Finite 𝒪 ↥M.1 := fun M => Module.Finite.iff_fg.mpr M.2.1

  have hφex : ∀ M : FullLattice 𝒪 K, ∃ φ : latticeBaseChange 𝒪 K V M →ₗ[V] V,
      Function.Surjective φ ∧ LinearMap.ker φ = N₀ M := by
    intro M
    haveI := hfin M
    obtain ⟨hinv, -⟩ := Module.Invertible.quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing V L (↥M.1)
      (d.line M) (d.invertible M)
    haveI := hinv
    haveI : Module.Free V (latticeBaseChange 𝒪 K V M ⧸ N₀ M) := inferInstance
    obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := V) (M := latticeBaseChange 𝒪 K V M ⧸ N₀ M)).mp
      inferInstance
    refine ⟨e.toLinearMap ∘ₗ (N₀ M).mkQ, e.surjective.comp (Submodule.mkQ_surjective _), ?_⟩
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]
  choose φ hφs hφk using hφex

  have h1π : ∀ (M : FullLattice 𝒪 K) (v : ↥M.1), (1 : V) ⊗ₜ[𝒪] (π • v) = 0 := by
    intro M v
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hV, TensorProduct.zero_tmul]
  have hgen : ∀ (M : FullLattice 𝒪 K) (I : Ideal V),
      (∀ v : ↥M.1, φ M ((1 : V) ⊗ₜ[𝒪] v) ∈ I) → I = ⊤ := by
    intro M I hI
    have hall : ∀ x, φ M x ∈ I := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact I.zero_mem
      | tmul a v =>
        have : a ⊗ₜ[𝒪] v = a • ((1 : V) ⊗ₜ[𝒪] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, LinearMap.map_smul, smul_eq_mul]
        exact I.mul_mem_left a (hI v)
      | add x y hx hy => rw [map_add]; exact I.add_mem hx hy
    rw [Ideal.eq_top_iff_one]
    obtain ⟨x, hx⟩ := hφs M 1
    rw [← hx]; exact hall x

  have hsup : ∀ (M : FullLattice 𝒪 K) (I : Ideal V) (x : latticeBaseChange 𝒪 K V M),
      x ∈ N₀ M ⊔ (I • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M)) ↔ φ M x ∈ I := by
    intro M I x
    constructor
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add, show φ M y = 0 from (by rw [← LinearMap.mem_ker, hφk]; exact hy), zero_add]
      refine Submodule.smul_induction_on hz (fun r hr n _ => ?_) (fun a b ha hb => ?_)
      · rw [LinearMap.map_smul, smul_eq_mul]; exact I.mul_mem_right _ hr
      · rw [map_add]; exact I.add_mem ha hb
    · intro hx
      obtain ⟨e, he⟩ := hφs M 1
      have : x = (x - φ M x • e) + φ M x • e := by abel
      rw [this]
      refine Submodule.add_mem_sup ?_ ?_
      · rw [← hφk, LinearMap.mem_ker, map_sub, LinearMap.map_smul, he, smul_eq_mul, mul_one, sub_self]
      · exact Submodule.smul_mem_smul hx Submodule.mem_top

  have hπK0 : πK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 hπ.ne_zero
  have hπsmul : ∀ (M : FullLattice 𝒪 K) (v : ↥M.1), ((π • v : ↥M.1) : Fin 2 → K) = πK • (v : Fin 2 → K) := by
    intro M v; rw [Submodule.coe_smul, algebraMap_smul]

  let KI : FullLattice 𝒪 K → Ideal V → Submodule 𝒪 (Fin 2 → K) := fun M I => V4Aux.KI M (φ M) I
  have hKI : ∀ (M : FullLattice 𝒪 K) (I : Ideal V) (v : ↥M.1),
      (v : Fin 2 → K) ∈ KI M I ↔ φ M ((1 : V) ⊗ₜ[𝒪] v) ∈ I := fun M I v => V4Aux.mem_KI M (φ M) I v
  have hKle : ∀ (M : FullLattice 𝒪 K) (I : Ideal V), KI M I ≤ M.1 := fun M I => V4Aux.KI_le M (φ M) I
  have hKπ : ∀ (M : FullLattice 𝒪 K) (I : Ideal V) (v : Fin 2 → K), v ∈ M.1 → πK • v ∈ KI M I := by
    intro M I v hv
    have := (hKI M I (π • ⟨v, hv⟩)).2 (by rw [h1π, map_zero]; exact I.zero_mem)
    rwa [hπsmul] at this
  have hKmono : ∀ (M : FullLattice 𝒪 K) (I J : Ideal V), I ≤ J → KI M I ≤ KI M J := by
    intro M I J hIJ w hw
    obtain ⟨h, h'⟩ := hw
    exact ⟨h, hIJ h'⟩
  have hKne : ∀ (M : FullLattice 𝒪 K) (I : Ideal V), I ≠ ⊤ → KI M I ≠ M.1 := by
    intro M I hI h
    apply hI
    apply hgen M I
    intro v
    have hv : (v : Fin 2 → K) ∈ KI M I := by rw [h]; exact v.2
    exact (hKI M I v).1 hv
  have hKfull : ∀ (M : FullLattice 𝒪 K) (I : Ideal V), IsFullLattice (KI M I) := by
    intro M I
    constructor
    · haveI : IsNoetherian 𝒪 ↥M.1 := isNoetherian_of_fg_of_noetherian _ M.2.1
      have h1 : (Submodule.comap M.1.subtype (KI M I)).FG := IsNoetherian.noetherian _
      have h2 := Submodule.FG.map (f := M.1.subtype) h1
      rwa [Submodule.map_comap_subtype, inf_eq_right.mpr (hKle M I)] at h2
    · rw [eq_top_iff, ← M.2.2]
      apply Submodule.span_le.2
      intro v hv
      have : v = πK⁻¹ • (πK • v) := by rw [smul_smul, inv_mul_cancel₀ hπK0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hKπ M I v hv))

  let Pi : FullLattice 𝒪 K → Submodule 𝒪 (Fin 2 → K) := fun M => V4Aux.PiLat πK M
  have hmemPi : ∀ (M : FullLattice 𝒪 K) (v : Fin 2 → K), v ∈ Pi M ↔ ∃ w : ↥M.1, v = πK • (w : Fin 2 → K) :=
    fun M v => V4Aux.mem_PiLat πK M v
  have hPile : ∀ (M : FullLattice 𝒪 K) (I : Ideal V), Pi M ≤ KI M I := by
    rintro M I v ⟨w, rfl⟩; exact hKπ M I w w.2

  have hincl1 : ∀ {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1) (v' : ↥M'.1),
      inclBaseChange V h ((1 : V) ⊗ₜ[𝒪] v') = (1 : V) ⊗ₜ[𝒪] (⟨(v' : Fin 2 → K), h v'.2⟩ : ↥M.1) := by
    intro M' M h v'
    rw [inclBaseChange, LinearMap.baseChange_tmul]
    rfl
  have hmono : ∀ {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1) (x : latticeBaseChange 𝒪 K V M'),
      x ∈ N₀ M' → inclBaseChange V h x ∈ N₀ M := by
    intro M' M h x hx
    rw [hmemN₀, rTensor_inclBaseChange f h x]
    exact d.mono h (Submodule.mem_map_of_mem ((hmemN₀ M' x).1 hx))
  have hfactor : ∀ {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1), ∃ c : V,
      ∀ x : latticeBaseChange 𝒪 K V M', φ M (inclBaseChange V h x) = c * φ M' x := by
    intro M' M h
    obtain ⟨e, he⟩ := hφs M' 1
    refine ⟨φ M (inclBaseChange V h e), fun x => ?_⟩
    have hx : x - φ M' x • e ∈ N₀ M' := by
      rw [← hφk, LinearMap.mem_ker, map_sub, LinearMap.map_smul, he, smul_eq_mul, mul_one, sub_self]
    have := hmono h _ hx
    rw [← hφk, LinearMap.mem_ker, map_sub, LinearMap.map_smul, map_sub, LinearMap.map_smul, sub_eq_zero] at this
    rw [this, smul_eq_mul, mul_comm]

  have sandwich : ∀ (M : FullLattice 𝒪 K) (R₁ R₂ : Submodule 𝒪 (Fin 2 → K)),
      Pi M ≤ R₁ → R₁ ≤ R₂ → R₂ ≤ M.1 → (∃ v ∈ R₁, v ∉ Pi M) → R₂ ≠ M.1 → R₁ = R₂ := by
    intro M R₁ R₂ hπ1 h12 h2M hne1 hne2
    refine FullLattice.eq_of_forall_smul_mem_of_le_of_le π hπ M R₁ R₂ (fun v hv => hπ1 ⟨⟨v, hv⟩, rfl⟩) h12 h2M ?_ hne2
    obtain ⟨v, hv, hvπ⟩ := hne1
    exact ⟨v, hv, fun w hw heq => hvπ ⟨⟨w, hw⟩, heq⟩⟩

  have hclause : ∀ (M : FullLattice 𝒪 K) (v : ↥M.1), φ M ((1 : V) ⊗ₜ[𝒪] v) ∉ 𝔭 →
      (1 : V) ⊗ₜ[𝒪] v ∉ N₀ M ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M)) :=
    fun M v h hmem => h ((hsup M 𝔭 _).1 hmem)
  have h𝔭top : 𝔭 ≠ ⊤ := h𝔭.ne_top

  have NR : ∀ M : FullLattice 𝒪 K, KI M ⊥ ≤ Pi M →
      ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
        (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
        (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
          (1 : V) ⊗ₜ[𝒪] v ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M |
              LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M}
            ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M))) ∧
        (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
          (1 : V) ⊗ₜ[𝒪] v' ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M' |
              LinearMap.rTensor (↥M'.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M'}
            ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M'))) := by
    intro M hM
    by_cases hcase : KI M 𝔭 ≤ Pi M
    ·
      refine ⟨M, M, le_rfl, ?_, ?_, ?_⟩
      · intro v; rw [← hπsmul]; exact (π • v).2
      · intro v hv; exact (hv v.2).elim
      · intro v' hv'
        apply hclause M v'
        intro h
        exact hv' ((hmemPi M _).1 (hcase ((hKI M 𝔭 v').2 h)))
    ·
      let C : FullLattice 𝒪 K := ⟨KI M 𝔭, hKfull M 𝔭⟩
      have hCM : C.1 ≤ M.1 := hKle M 𝔭
      refine ⟨C, M, hCM, fun v => hKπ M 𝔭 v v.2, fun v hv => ?_, fun v' hv' => ?_⟩
      · apply hclause M v
        intro h; exact hv ((hKI M 𝔭 v).2 h)
      · apply hclause C v'
        intro hv'𝔭
        obtain ⟨c, hc⟩ := hfactor hCM
        obtain ⟨u, huM, huC⟩ : ∃ u ∈ M.1, u ∉ C.1 := by
          by_contra hall
          push Not at hall
          exact hKne M 𝔭 h𝔭top (le_antisymm (hKle M 𝔭) fun u hu => hall u hu)
        obtain ⟨v₀, hv₀C, hv₀π⟩ : ∃ v₀ ∈ C.1, v₀ ∉ Pi M := SetLike.not_le_iff_exists.1 hcase

        have hc0 : c ≠ 0 := by
          intro hc0
          apply hv₀π
          apply hM
          refine (hKI M ⊥ ⟨v₀, hCM hv₀C⟩).2 ?_
          rw [Ideal.mem_bot]
          have := hc ((1 : V) ⊗ₜ[𝒪] (⟨v₀, hv₀C⟩ : ↥C.1))
          rw [hincl1 hCM, hc0, zero_mul] at this
          exact this

        have hB : ∀ w : ↥C.1, φ C ((1 : V) ⊗ₜ[𝒪] w) = 0 → (w : Fin 2 → K) ∈ Pi M := by
          intro w hw
          apply hM
          refine (hKI M ⊥ ⟨w, hCM w.2⟩).2 ?_
          rw [Ideal.mem_bot]
          have := hc ((1 : V) ⊗ₜ[𝒪] w)
          rw [hincl1 hCM, hw, mul_zero] at this
          exact this

        have hπuC : πK • u ∈ C.1 := hKπ M 𝔭 u huM
        have hπu0 : πK • u ∈ KI C ⊥ := by
          refine (hKI C ⊥ ⟨πK • u, hπuC⟩).2 ?_
          rw [Ideal.mem_bot]
          have h0 : φ M (inclBaseChange V hCM ((1 : V) ⊗ₜ[𝒪] (⟨πK • u, hπuC⟩ : ↥C.1))) = 0 := by
            rw [hincl1 hCM]
            have : (⟨((⟨πK • u, hπuC⟩ : ↥C.1) : Fin 2 → K), hCM hπuC⟩ : ↥M.1) = π • ⟨u, huM⟩ :=
              Subtype.ext (by rw [hπsmul])
            rw [this, h1π, map_zero]
          have := hc ((1 : V) ⊗ₜ[𝒪] (⟨πK • u, hπuC⟩ : ↥C.1))
          rw [h0] at this
          exact (mul_eq_zero.1 this.symm).resolve_left hc0
        have hπuπC : πK • u ∉ Pi C := by
          rintro ⟨w, hw⟩
          apply huC
          have : u = (w : Fin 2 → K) := smul_right_injective (Fin 2 → K) hπK0 hw
          rw [this]; exact w.2

        have hSW := sandwich C (KI C ⊥) (KI C 𝔭) (hPile C ⊥) (hKmono C ⊥ 𝔭 bot_le) (hKle C 𝔭)
          ⟨πK • u, hπu0, hπuπC⟩ (hKne C 𝔭 h𝔭top)
        have h1' : (v' : Fin 2 → K) ∈ KI C ⊥ := by rw [hSW]; exact (hKI C 𝔭 v').2 hv'𝔭
        have h2' : φ C ((1 : V) ⊗ₜ[𝒪] v') = 0 := (Ideal.mem_bot).1 ((hKI C ⊥ v').1 h1')
        obtain ⟨w, hw⟩ := (hmemPi M _).1 (hB v' h2')
        exact hv' ⟨w, hw⟩

  obtain ⟨B, A, hBA, hπAB, h1, h2⟩ := d.nondeg ⊥ Ideal.bot_prime
  have h1φ : ∀ v : ↥A.1, (v : Fin 2 → K) ∉ B.1 → φ A ((1 : V) ⊗ₜ[𝒪] v) ≠ 0 := by
    intro v hv hzero
    apply h1 v hv
    have hmem : (1 : V) ⊗ₜ[𝒪] v ∈ N₀ A := by rw [← hφk, LinearMap.mem_ker]; exact hzero
    have h2' := (hmemN₀ A _).1 hmem
    rw [rTensor_one_tmul f A v] at h2'
    exact Submodule.mem_sup_left h2'
  have h2φ : ∀ v' : ↥B.1, (¬ ∃ w : ↥A.1, (v' : Fin 2 → K) = πK • (w : Fin 2 → K)) →
      φ B ((1 : V) ⊗ₜ[𝒪] v') ≠ 0 := by
    intro v' hv' hzero
    apply h2 v' hv'
    have hmem : (1 : V) ⊗ₜ[𝒪] v' ∈ N₀ B := by rw [← hφk, LinearMap.mem_ker]; exact hzero
    have h2' := (hmemN₀ B _).1 hmem
    rw [rTensor_one_tmul f B v'] at h2'
    exact Submodule.mem_sup_left h2'
  have hKA : KI A ⊥ ≤ B.1 := by
    intro v hv
    obtain ⟨hvA, h0⟩ := hv
    by_contra hvB
    exact h1φ ⟨v, hvA⟩ hvB ((Ideal.mem_bot).1 h0)
  have hKB : KI B ⊥ ≤ Pi A := by
    intro v hv
    obtain ⟨hvB, h0⟩ := hv
    by_contra hvπ
    exact h2φ ⟨v, hvB⟩ (fun hex => hvπ ((hmemPi A v).2 hex)) ((Ideal.mem_bot).1 h0)
  have hPiA_le_B : Pi A ≤ B.1 := by
    rintro v ⟨w, rfl⟩; exact hπAB w
  have hPiB_le_PiA : Pi B ≤ Pi A := by
    rintro v ⟨w, rfl⟩; exact ⟨⟨w, hBA w.2⟩, rfl⟩
  by_cases hA : KI A ⊥ ≤ Pi A
  · exact NR A hA

  obtain ⟨v₁, hv₁K, hv₁π⟩ : ∃ v₁ ∈ KI A ⊥, v₁ ∉ Pi A := SetLike.not_le_iff_exists.1 hA
  have hv₁B : v₁ ∈ B.1 := hKA hv₁K
  have hBneA : B.1 ≠ A.1 := by
    intro hBA'
    have hBeq : B = A := Subtype.ext hBA'
    subst hBeq
    obtain ⟨hv₁A, h0⟩ := hv₁K
    exact h2φ ⟨v₁, hv₁A⟩ (fun hex => hv₁π ((hmemPi _ v₁).2 hex)) ((Ideal.mem_bot).1 h0)
  have hKAeq : KI A ⊥ = B.1 := sandwich A (KI A ⊥) B.1 (hPile A ⊥) hKA hBA ⟨v₁, hv₁K, hv₁π⟩ hBneA
  by_cases hB : KI B ⊥ ≤ Pi B
  · exact NR B hB

  obtain ⟨v₂, hv₂K, hv₂π⟩ : ∃ v₂ ∈ KI B ⊥, v₂ ∉ Pi B := SetLike.not_le_iff_exists.1 hB
  have hPiAneB : Pi A ≠ B.1 := by
    intro h; apply hv₁π; rw [h]; exact hv₁B
  have hKBeq : KI B ⊥ = Pi A := sandwich B (KI B ⊥) (Pi A) (hPile B ⊥) hKB hPiA_le_B ⟨v₂, hv₂K, hv₂π⟩ hPiAneB
  obtain ⟨u, huA, huB⟩ : ∃ u ∈ A.1, u ∉ B.1 :=
    SetLike.not_le_iff_exists.1 (fun h => hBneA (le_antisymm hBA h))
  have hK𝔭A : B.1 = KI A 𝔭 :=
    sandwich A B.1 (KI A 𝔭) hPiA_le_B (by have h := hKmono A ⊥ 𝔭 bot_le; rw [hKAeq] at h; exact h) (hKle A 𝔭)
      ⟨v₁, hv₁B, hv₁π⟩ (hKne A 𝔭 h𝔭top)
  have hπuπB : πK • u ∉ Pi B := by
    rintro ⟨w, hw⟩
    apply huB
    have : u = (w : Fin 2 → K) := smul_right_injective (Fin 2 → K) hπK0 hw
    rw [this]; exact w.2
  have hK𝔭B : Pi A = KI B 𝔭 :=
    sandwich B (Pi A) (KI B 𝔭) hPiB_le_PiA (by have h := hKmono B ⊥ 𝔭 bot_le; rw [hKBeq] at h; exact h) (hKle B 𝔭)
      ⟨πK • u, ⟨⟨u, huA⟩, rfl⟩, hπuπB⟩ (hKne B 𝔭 h𝔭top)
  refine ⟨B, A, hBA, hπAB, fun v hv => ?_, fun v' hv' => ?_⟩
  · apply hclause A v
    intro h
    apply hv
    rw [hK𝔭A]; exact (hKI A 𝔭 v).2 h
  · apply hclause B v'
    intro h
    apply hv'
    have : (v' : Fin 2 → K) ∈ Pi A := by rw [hK𝔭B]; exact (hKI B 𝔭 v').2 h
    exact (hmemPi A _).1 this

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V] (hV : algebraMap 𝒪 V π = 0)
    (L : Type) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (d : DeligneDatum (K := K) π L) (𝔭 : Ideal V) (h𝔭 : 𝔭.IsPrime) :
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : V) ⊗ₜ[𝒪] v ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M |
            LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M}
          ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : V) ⊗ₜ[𝒪] v' ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M' |
            LinearMap.rTensor (↥M'.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M'}
          ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M'))) :=
  V4_main π hπ V hV L d 𝔭 h𝔭

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_edge_nondeg_saturation_of_valuationRing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_edge_nondeg_saturation_of_valuationRing (solution)
