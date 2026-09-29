-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/044be96c-edaf-52b3-9da0-8ce617e9af17

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_isPullback_inEdgeChart_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective
import Theorems.Thm_IsDiscreteValuationRing_of_isAdicComplete_span_singleton_of_isMaximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace ASM21
namespace SRC

section infra
variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B] (S : Subalgebra 𝒪 B) (fS : ↥S)

theorem powers_le_comap : Submonoid.powers fS ≤ Submonoid.comap S.val.toRingHom (Submonoid.powers (fS : B)) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

noncomputable def jLoc : Localization.Away fS →ₐ[𝒪] Localization.Away (fS : B) :=
  { toRingHom := IsLocalization.map (M := Submonoid.powers fS) (T := Submonoid.powers (fS : B)) (Localization.Away (fS : B)) S.val.toRingHom
      (powers_le_comap S fS)
    commutes' := fun o => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply 𝒪 (↥S) (Localization.Away fS), IsLocalization.map_eq,
        IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (fS : B))]
      rfl }

theorem jLoc_algebraMap (a : ↥S) : jLoc S fS (algebraMap (↥S) _ a) = algebraMap B _ (a : B) := by
  show IsLocalization.map (M := Submonoid.powers fS) (T := Submonoid.powers (fS : B)) (Localization.Away (fS : B)) S.val.toRingHom
    (powers_le_comap S fS) (algebraMap (↥S) _ a) = _
  rw [IsLocalization.map_eq]; rfl

theorem jLoc_injective : Function.Injective (jLoc S fS) := by
  have hmap : Submonoid.map S.val.toRingHom (Submonoid.powers fS) = Submonoid.powers (fS : B) := by
    rw [Submonoid.map_powers]; rfl
  haveI : IsLocalization (Submonoid.map S.val.toRingHom (Submonoid.powers fS)) (Localization.Away (fS : B)) := by
    rw [hmap]; exact inferInstance
  exact IsLocalization.map_injective_of_injective (Submonoid.powers fS) (Localization.Away fS) (Localization.Away (fS : B))
    (g := S.val.toRingHom) (fun a b h => Subtype.ext h)

end infra

theorem local_descent
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (S : Subalgebra 𝒪 B) (fS : ↥S) (d : DeligneDatum (K := K) π B) (h : Matrix.GeneralLinearGroup (Fin 2) K)
    (d' : DeligneDatum (K := K) π (Localization.Away (fS : B)))
    (hpb : DeligneDatum.IsPullback (K := K) (π := π) _ h
      ((Omega K π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (fS : B))) d) d')
    (hch : d'.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K))
    (x : chartERing 𝒪 π q →ₐ[𝒪] Localization.Away (fS : B))
    (hx₁ : d'.line (stdFullLattice K) =
      Submodule.span (Localization.Away (fS : B)) {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : Localization.Away (fS : B)) ⊗ₜ[𝒪] stdBasisVec K 1})
    (hx₂ : d'.line (FullLattice.act g (stdFullLattice K)) =
      (Submodule.span (Localization.Away (fS : B)) {(1 : Localization.Away (fS : B)) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange (Localization.Away (fS : B)) g (stdFullLattice K)).toLinearMap)
    (hξ : x (chartERing.ξ 𝒪 π q) ∈ Set.range (jLoc S fS)) (hη : x (chartERing.η 𝒪 π q) ∈ Set.range (jLoc S fS))
    (hw : ∃ w ∈ Set.range (jLoc S fS), w * ((x (chartERing.ξ 𝒪 π q) ^ (q - 1) - 1) * (x (chartERing.η 𝒪 π q) ^ (q - 1) - 1)) = 1) :
    ∃ e' : DeligneDatum (K := K) π (Localization.Away fS),
      (Omega K π).map (jLoc S fS) e' = (Omega K π).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (fS : B))) d := by
  classical
  set CB := Localization.Away (fS : B) with hCB
  set CS := Localization.Away fS with hCS
  set j := jLoc S fS with hj
  have hjinj : Function.Injective j := jLoc_injective S fS

  obtain ⟨u', hu'⟩ := hξ
  obtain ⟨v', hv'⟩ := hη
  obtain ⟨w, ⟨w', hw'⟩, hw⟩ := hw
  have huv : u' * v' = algebraMap 𝒪 CS π := by
    apply hjinj
    rw [map_mul, hu', hv', ← map_mul, chartERing.ξ_mul_η, AlgHom.commutes, AlgHom.commutes]
  have hdisc : IsUnit ((u' ^ (q - 1) - 1) * (v' ^ (q - 1) - 1)) := by
    have hprod : w' * ((u' ^ (q - 1) - 1) * (v' ^ (q - 1) - 1)) = 1 := hjinj (by
      rw [map_mul, map_one, hw', map_mul, map_sub, map_sub, map_pow, map_pow, map_one, hu', hv']
      exact hw)
    exact ⟨⟨_, w', by rw [mul_comm] at hprod; exact hprod, hprod⟩, rfl⟩
  let pt : (chartE 𝒪 π q).obj CS := ⟨(u', v'), huv, isUnit_of_mul_isUnit_left hdisc, isUnit_of_mul_isUnit_right hdisc⟩
  let y : chartERing 𝒪 π q →ₐ[𝒪] CS := chartERing.lift pt
  have hyξ : y (chartERing.ξ 𝒪 π q) = u' := chartERing.lift_ξ pt
  have hyη : y (chartERing.η 𝒪 π q) = v' := chartERing.lift_η pt

  have hSπ : IsNilpotent (algebraMap 𝒪 CS π) := by
    obtain ⟨n, hn⟩ := hB
    refine ⟨n, ?_⟩
    rw [IsScalarTower.algebraMap_apply 𝒪 (↥S) CS, ← map_pow]
    have : (algebraMap 𝒪 (↥S) π) ^ n = 0 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow]; show (algebraMap 𝒪 B π) ^ n = 0; exact hn)
    rw [this, map_zero]
  obtain ⟨e₀, he₀₁, he₀₂, he₀ch⟩ :=
    exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent π hπ q hq g hg CS hSπ y

  have hspan : ∀ (M : FullLattice 𝒪 K) (z : latticeBaseChange 𝒪 K CS M),
      lineBaseChange j M (Submodule.span CS {z}) = Submodule.span CB {LinearMap.rTensor (↥M.1) j.toLinearMap z} := by
    intro M z
    apply le_antisymm
    · rw [lineBaseChange, Submodule.span_le]
      rintro _ ⟨n, hn, rfl⟩
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hn
      rw [rTensor_smul_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨z, Submodule.mem_span_singleton_self z, rfl⟩
  have hspan_act : ∀ (M : FullLattice 𝒪 K) (N : Submodule CS (latticeBaseChange 𝒪 K CS M)),
      lineBaseChange j (FullLattice.act g M) (N.map (actBaseChange CS g M).toLinearMap) =
        (lineBaseChange j M N).map (actBaseChange CB g M).toLinearMap := by
    intro M N
    rw [lineBaseChange, lineBaseChange, Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]
    congr 1
    apply Set.image_congr
    intro z _
    exact rTensor_actBaseChange j g M z
  have he₀map : (Omega K π).map j e₀ = d' := by
    apply DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d' _ _ _ hch
    · show lineBaseChange j _ (e₀.line (stdFullLattice K)) = d'.line (stdFullLattice K)
      rw [he₀₁, hspan, hx₁, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        AlgHom.toLinearMap_apply, map_one, hyξ, hu']
    · show lineBaseChange j _ (e₀.line (FullLattice.act g (stdFullLattice K))) = d'.line (FullLattice.act g (stdFullLattice K))
      rw [he₀₂, hspan_act, hspan, hx₂, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        AlgHom.toLinearMap_apply, map_one, hyη, hv']

  have hd' : d' = DeligneDatum.pullback π CB h ((Omega K π).map (IsScalarTower.toAlgHom 𝒪 B CB) d) :=
    DeligneDatum.ext' (funext hpb)
  have hact : ∀ (X : DeligneDatum (K := K) π CB),
      DeligneDatum.pullback π CB h⁻¹ (DeligneDatum.pullback π CB h X) = X := by
    intro X
    have h1 : DeligneDatum.pullback π CB h X = (Omega.action K π).act CB h⁻¹ X := by
      show DeligneDatum.pullback π CB h X = DeligneDatum.pullback π CB (h⁻¹)⁻¹ X; rw [inv_inv]
    have h2 : DeligneDatum.pullback π CB h⁻¹ ((Omega.action K π).act CB h⁻¹ X) =
        (Omega.action K π).act CB h ((Omega.action K π).act CB h⁻¹ X) := by
      show _ = DeligneDatum.pullback π CB h⁻¹ _; rfl
    rw [h1, h2, ← (Omega.action K π).act_mul, mul_inv_cancel, (Omega.action K π).act_one]
  refine ⟨DeligneDatum.pullback π CS h⁻¹ e₀, ?_⟩
  show DeligneDatum.map π j (DeligneDatum.pullback π CS h⁻¹ e₀) = _
  rw [DeligneDatum.map_pullback]
  have : DeligneDatum.map π j e₀ = d' := he₀map
  rw [this, hd', hact]

set_option maxHeartbeats 8000000 in

theorem part1_flow
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (ψ : Onr →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B) :
    ∃ (s : Finset B) (S : Subalgebra 𝒪 B) (_ : S = Algebra.adjoin 𝒪 (Set.range ψ ∪ (↑s : Set B)))
      (ψ₀ : Onr →ₐ[𝒪] ↥S) (e : DeligneDatum (K := K₀) π ↥S),
      S.val.comp ψ₀ = ψ ∧ (Omega K₀ π).map S.val e = d := by
  classical
  haveI := hdvr
  haveI : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)

  have hπK : algebraMap 𝒪 K₀ π ≠ 0 := fun h0 => hπ.ne_zero ((IsFractionRing.injective 𝒪 K₀) (by rw [h0, map_zero]))
  let g : Matrix.GeneralLinearGroup (Fin 2) K₀ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
      (by rw [Matrix.det_diagonal]; simp [hπK])
  have hg : (g : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1] := rfl

  obtain ⟨k, f, hf, h, hcov⟩ :=
    DeligneDatum.exists_finite_cover_isPullback_inEdgeChart_of_finite π hπ g hg B hB d
  have hBloc : ∀ i, IsNilpotent (algebraMap 𝒪 (Localization.Away (f i)) π) := fun i => by
    rw [IsScalarTower.algebraMap_apply 𝒪 B]; exact hB.map _
  have hcov' := fun i => hcov i (Localization.Away (f i))
  choose d' hd'pb hd'ch using hcov'
  have hchart := fun i =>
    DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite π hπ r hres g hg (Localization.Away (f i))
      (hBloc i) (d' i) (hd'ch i)
  choose xc hxc₁ hxc₂ using hchart

  have hnum := fun i => IsLocalization.surj (Submonoid.powers (f i)) (xc i (chartERing.ξ 𝒪 π r))
  have hnum' := fun i => IsLocalization.surj (Submonoid.powers (f i)) (xc i (chartERing.η 𝒪 π r))
  choose aξ haξ using hnum
  choose aη haη using hnum'
  have hdisc : ∀ i, IsUnit ((xc i (chartERing.ξ 𝒪 π r) ^ (r - 1) - 1) * (xc i (chartERing.η 𝒪 π r) ^ (r - 1) - 1)) := by
    intro i
    have := (chartERing.isUnit_discr 𝒪 π r).map (xc i)
    simpa using this
  choose w hw using fun i => (hdisc i).exists_left_inv
  have hnum'' := fun i => IsLocalization.surj (Submonoid.powers (f i)) (w i)
  choose aw haw using hnum''

  obtain ⟨c, hc⟩ : ∃ c : Fin k → B, ∑ i, c i * f i = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (hf.symm ▸ Submodule.mem_top : (1 : B) ∈ Ideal.span (Set.range f))

  let s : Finset B := (Finset.univ.image f ∪ Finset.univ.image c) ∪
    ((Finset.univ.image fun i => (aξ i).1) ∪ (Finset.univ.image fun i => (aη i).1) ∪ (Finset.univ.image fun i => (aw i).1))
  let S : Subalgebra 𝒪 B := Algebra.adjoin 𝒪 (Set.range ψ ∪ (↑s : Set B))
  have hsS : ∀ b ∈ s, b ∈ S := fun b hb => Algebra.subset_adjoin (Or.inr hb)
  have hfS : ∀ i, f i ∈ S := fun i => hsS _ (by simp [s])
  have hcS : ∀ i, c i ∈ S := fun i => hsS _ (by simp [s])
  have haξS : ∀ i, (aξ i).1 ∈ S := fun i => hsS _ (by simp [s])
  have haηS : ∀ i, (aη i).1 ∈ S := fun i => hsS _ (by simp [s])
  have hawS : ∀ i, (aw i).1 ∈ S := fun i => hsS _ (by simp [s])
  have hψS : ∀ o, ψ o ∈ S := fun o => Algebra.subset_adjoin (Or.inl ⟨o, rfl⟩)
  let ψ₀ : Onr →ₐ[𝒪] ↥S := ψ.codRestrict S hψS
  let fS : Fin k → ↥S := fun i => ⟨f i, hfS i⟩

  have hrange : ∀ (i : Fin k) (u : Localization.Away (f i)) (a : B) (m : Submonoid.powers (f i)),
      a ∈ S → u * algebraMap B _ (m : B) = algebraMap B _ a → u ∈ Set.range (jLoc S (fS i)) := by
    intro i u a m ha hu
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 m.2
    have hu' : u = IsLocalization.mk' (Localization.Away (f i)) a m := (IsLocalization.eq_mk'_iff_mul_eq).2 hu
    refine ⟨IsLocalization.mk' (Localization.Away (fS i)) (⟨a, ha⟩ : ↥S) (⟨fS i ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩ : Submonoid.powers (fS i)), ?_⟩
    rw [hu']
    show IsLocalization.map (M := Submonoid.powers (fS i)) (T := Submonoid.powers (f i)) (Localization.Away (f i)) S.val.toRingHom
      (powers_le_comap S (fS i)) _ = _
    rw [IsLocalization.map_mk']
    congr 1
    · exact Subtype.ext (by simp [fS, hn])
  have hloc := fun i => local_descent π hπ r hres g hg hB S (fS i) d (h i) (d' i) (hd'pb i) (hd'ch i) (xc i) (hxc₁ i) (hxc₂ i)
    (hrange i _ _ _ (haξS i) (haξ i)) (hrange i _ _ _ (haηS i) (haη i))
    ⟨w i, hrange i _ _ _ (hawS i) (haw i), hw i⟩
  choose e' he' using hloc

  have hfS1 : ∑ i, (⟨c i, hcS i⟩ : ↥S) * fS i = 1 := Subtype.ext (by simpa [fS] using hc)
  have hfStop : Ideal.span (Set.range fS) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hfS1]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  let ρ₁ : ∀ i j : Fin k, Localization.Away (fS i) →ₐ[↥S] Localization.Away (fS i * fS j) := fun i j =>
    { toRingHom := IsLocalization.Away.awayToAwayRight (fS i) (fS j)
      commutes' := fun a => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
        exact IsLocalization.Away.lift_eq _ _ a }
  let ρ₂ : ∀ i j : Fin k, Localization.Away (fS j) →ₐ[↥S] Localization.Away (fS i * fS j) := fun i j =>
    { toRingHom := IsLocalization.Away.awayToAwayLeft (fS j) (fS i)
      commutes' := fun a => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
        exact IsLocalization.Away.lift_eq _ _ a }
  have hcompat : ∀ i j : Fin k, (Omega K₀ π).map ((ρ₁ i j).restrictScalars 𝒪) (e' i) = (Omega K₀ π).map ((ρ₂ i j).restrictScalars 𝒪) (e' j) := by
    intro i j

    let T := Localization.Away ((fS i * fS j : ↥S) : B)
    have hunitT : IsUnit (algebraMap B T ((fS i * fS j : ↥S) : B)) := IsLocalization.Away.algebraMap_isUnit _
    have hui : IsUnit (algebraMap B T (f i)) :=
      isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hunitT)
    have huj : IsUnit (algebraMap B T (f j)) :=
      isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hunitT)
    let θi : Localization.Away (f i) →ₐ[𝒪] T :=
      { toRingHom := IsLocalization.Away.lift (f i) (g := algebraMap B T) hui
        commutes' := fun o => by
          simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
          rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f i)), IsLocalization.Away.lift_eq,
            ← IsScalarTower.algebraMap_apply] }
    let θj : Localization.Away (f j) →ₐ[𝒪] T :=
      { toRingHom := IsLocalization.Away.lift (f j) (g := algebraMap B T) huj
        commutes' := fun o => by
          simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
          rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f j)), IsLocalization.Away.lift_eq,
            ← IsScalarTower.algebraMap_apply] }
    have hθi : θi.comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) = IsScalarTower.toAlgHom 𝒪 B T := by
      apply AlgHom.ext; intro b
      show IsLocalization.Away.lift (f i) hui (algebraMap B (Localization.Away (f i)) b) = algebraMap B T b
      exact IsLocalization.Away.lift_eq (f i) hui b
    have hθj : θj.comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) = IsScalarTower.toAlgHom 𝒪 B T := by
      apply AlgHom.ext; intro b
      show IsLocalization.Away.lift (f j) huj (algebraMap B (Localization.Away (f j)) b) = algebraMap B T b
      exact IsLocalization.Away.lift_eq (f j) huj b

    have hsq₁ : (jLoc S (fS i * fS j)).comp ((ρ₁ i j).restrictScalars 𝒪) = θi.comp (jLoc S (fS i)) := by
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers (fS i))
      ext a
      show jLoc S (fS i * fS j) (ρ₁ i j (algebraMap (↥S) _ a)) = θi (jLoc S (fS i) (algebraMap (↥S) _ a))
      rw [(ρ₁ i j).commutes, jLoc_algebraMap, jLoc_algebraMap]
      exact (IsLocalization.Away.lift_eq (f i) hui (a : B)).symm
    have hsq₂ : (jLoc S (fS i * fS j)).comp ((ρ₂ i j).restrictScalars 𝒪) = θj.comp (jLoc S (fS j)) := by
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers (fS j))
      ext a
      show jLoc S (fS i * fS j) (ρ₂ i j (algebraMap (↥S) _ a)) = θj (jLoc S (fS j) (algebraMap (↥S) _ a))
      rw [(ρ₂ i j).commutes, jLoc_algebraMap, jLoc_algebraMap]
      exact (IsLocalization.Away.lift_eq (f j) huj (a : B)).symm
    apply Omega.map_injective_of_injective π (jLoc S (fS i * fS j)) (jLoc_injective S _)
    show (Omega K₀ π).map (jLoc S (fS i * fS j)) ((Omega K₀ π).map ((ρ₁ i j).restrictScalars 𝒪) (e' i)) =
      (Omega K₀ π).map (jLoc S (fS i * fS j)) ((Omega K₀ π).map ((ρ₂ i j).restrictScalars 𝒪) (e' j))
    rw [← (Omega K₀ π).map_comp, ← (Omega K₀ π).map_comp, hsq₁, hsq₂, (Omega K₀ π).map_comp, (Omega K₀ π).map_comp,
      he' i, he' j, ← (Omega K₀ π).map_comp, ← (Omega K₀ π).map_comp, hθi, hθj]
  obtain ⟨e, he, -⟩ := Omega.existsUnique_glue_of_span_eq_top π (↥S) fS hfStop (fun i => Localization.Away (fS i))
    (fun i j => Localization.Away (fS i * fS j)) ρ₁ ρ₂ e' hcompat
  refine ⟨s, S, rfl, ψ₀, e, AlgHom.ext fun o => rfl, ?_⟩

  let τ : ∀ i : Fin k, B →ₐ[𝒪] Localization.Away (f i) := fun i => IsScalarTower.toAlgHom 𝒪 B _
  let σB₁ : ∀ i j : Fin k, Localization.Away (f i) →ₐ[B] Localization.Away (f i * f j) := fun i j =>
    { toRingHom := IsLocalization.Away.awayToAwayRight (f i) (f j)
      commutes' := fun a => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
        exact IsLocalization.Away.lift_eq _ _ a }
  let σB₂ : ∀ i j : Fin k, Localization.Away (f j) →ₐ[B] Localization.Away (f i * f j) := fun i j =>
    { toRingHom := IsLocalization.Away.awayToAwayLeft (f j) (f i)
      commutes' := fun a => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
        exact IsLocalization.Away.lift_eq _ _ a }
  have hτ₁ : ∀ i j, ((σB₁ i j).restrictScalars 𝒪).comp (τ i) = IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i * f j)) := by
    intro i j; apply AlgHom.ext; intro b
    show σB₁ i j (algebraMap B _ b) = algebraMap B _ b
    exact (σB₁ i j).commutes b
  have hτ₂ : ∀ i j, ((σB₂ i j).restrictScalars 𝒪).comp (τ j) = IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i * f j)) := by
    intro i j; apply AlgHom.ext; intro b
    show σB₂ i j (algebraMap B _ b) = algebraMap B _ b
    exact (σB₂ i j).commutes b
  have hcompatB : ∀ i j : Fin k, (Omega K₀ π).map ((σB₁ i j).restrictScalars 𝒪) ((Omega K₀ π).map (τ i) d) =
      (Omega K₀ π).map ((σB₂ i j).restrictScalars 𝒪) ((Omega K₀ π).map (τ j) d) := by
    intro i j
    rw [← (Omega K₀ π).map_comp, ← (Omega K₀ π).map_comp, hτ₁, hτ₂]
  obtain ⟨d₀, hd₀, huniq⟩ := Omega.existsUnique_glue_of_span_eq_top π B f hf (fun i => Localization.Away (f i))
    (fun i j => Localization.Away (f i * f j)) σB₁ σB₂ (fun i => (Omega K₀ π).map (τ i) d) hcompatB
  have hd : d = d₀ := huniq d (fun i => rfl)
  have hval : ∀ i, (τ i).comp S.val = (jLoc S (fS i)).comp (IsScalarTower.toAlgHom 𝒪 (↥S) (Localization.Away (fS i))) := by
    intro i; apply AlgHom.ext; intro b
    show algebraMap B (Localization.Away (f i)) (b : B) = jLoc S (fS i) (algebraMap (↥S) (Localization.Away (fS i)) b)
    rw [jLoc_algebraMap]
  have he2 : (Omega K₀ π).map S.val e = d₀ := by
    apply huniq
    intro i
    rw [← (Omega K₀ π).map_comp, hval, (Omega K₀ π).map_comp, he i, he' i]
  rw [he2, ← hd]

theorem part1
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    (∀ x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      ∃ (s : Finset B) (S : Subalgebra 𝒪 B) (_ : S = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑s : Set B)))
        (x₀ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S), (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val x₀ = x) := by
  classical
  intro x
  obtain ⟨s, S, hS, ψ₀, e, hψ, he⟩ := part1_flow 𝒪 hdvr π hπ hres K₀ Onr B hB x.1 x.2
  refine ⟨s, S, hS, (ψ₀, e), ?_⟩
  show ((S.val.comp ψ₀, (Omega K₀ π).map S.val e) : (Onr →ₐ[𝒪] B) × DeligneDatum (K := K₀) π B) = x
  rw [hψ, he]; rfl

theorem part2
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    (∀ (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (s₁ s₂ : Finset B) (S₁ S₂ : Subalgebra 𝒪 B),
      S₁ = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑s₁ : Set B)) →
      S₂ = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑s₂ : Set B)) →
      ∀ (x₁ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S₁) (x₂ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S₂),
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S₁.val x₁ = x → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S₂.val x₂ = x →
      ∃ (s₃ : Finset B) (S₃ : Subalgebra 𝒪 B) (_ : S₃ = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑s₃ : Set B)))
        (h₁ : S₁ ≤ S₃) (h₂ : S₂ ≤ S₃),
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h₁) x₁ = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h₂) x₂) := by
  classical
  intro x s₁ s₂ S₁ S₂ hS₁ hS₂ x₁ x₂ hx₁ hx₂

  refine ⟨s₁ ∪ s₂, Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑(s₁ ∪ s₂) : Set B)), rfl, ?_, ?_, ?_⟩
  · rw [hS₁]; apply Algebra.adjoin_mono; intro b hb
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (by rw [Finset.coe_union]; exact Or.inl hb)
  · rw [hS₂]; apply Algebra.adjoin_mono; intro b hb
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (by rw [Finset.coe_union]; exact Or.inr hb)
  ·
    set S₃ := Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑(s₁ ∪ s₂) : Set B)) with hS₃

    have hle₁ : S₁ ≤ S₃ := by
      rw [hS₁]; apply Algebra.adjoin_mono; intro b hb
      rcases hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr (by rw [Finset.coe_union]; exact Or.inl hb)
    have hle₂ : S₂ ≤ S₃ := by
      rw [hS₂]; apply Algebra.adjoin_mono; intro b hb
      rcases hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr (by rw [Finset.coe_union]; exact Or.inr hb)
    show (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion hle₁) x₁ =
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion hle₂) x₂
    have h1c := congrArg Prod.fst hx₁
    have h2c := congrArg Prod.fst hx₂
    have h1d := congrArg Prod.snd hx₁
    have h2d := congrArg Prod.snd hx₂
    apply Prod.ext
    ·
      show (Subalgebra.inclusion hle₁).comp x₁.1 = (Subalgebra.inclusion hle₂).comp x₂.1
      apply AlgHom.ext; intro o; apply Subtype.ext
      show ((S₁.val.comp x₁.1) o : B) = (S₂.val.comp x₂.1) o
      change S₁.val.comp x₁.1 = x.1 at h1c
      change S₂.val.comp x₂.1 = x.1 at h2c
      rw [h1c, h2c]
    ·
      apply Omega.map_injective_of_injective π S₃.val (fun a b h => Subtype.ext h)
      show (Omega K₀ π).map S₃.val ((Omega K₀ π).map (Subalgebra.inclusion hle₁) x₁.2) =
        (Omega K₀ π).map S₃.val ((Omega K₀ π).map (Subalgebra.inclusion hle₂) x₂.2)
      rw [← (Omega K₀ π).map_comp, ← (Omega K₀ π).map_comp, Subalgebra.val_comp_inclusion, Subalgebra.val_comp_inclusion]
      change (Omega K₀ π).map S₁.val x₁.2 = x.2 at h1d
      change (Omega K₀ π).map S₂.val x₂.2 = x.2 at h2d
      rw [h1d, h2d]

theorem part3
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    (∀ (ψ : Onr →ₐ[𝒪] B) (s : Finset B) (S : Subalgebra 𝒪 B),
      S = Algebra.adjoin 𝒪 (Set.range ψ ∪ (↑s : Set B)) → IsNoetherianRing ↥S) := by
  classical
  intro ψ s S hS

  have hϖ : algebraMap 𝒪 Onr π ≠ 0 := by
    intro h0
    have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hr
    have : ((r : ℕ) : Onr) = 0 := by
      rw [← map_natCast (algebraMap 𝒪 Onr), ← hc, map_mul, h0, mul_zero]
    exact (Fact.out : r.Prime).ne_zero (by exact_mod_cast this)
  haveI : IsDiscreteValuationRing Onr :=
    IsDiscreteValuationRing.of_isAdicComplete_span_singleton_of_isMaximal Onr _ hϖ hOnr_complete hOnr_max
  haveI : IsNoetherianRing Onr := inferInstance

  letI : Algebra Onr B := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower 𝒪 Onr B := IsScalarTower.of_algebraMap_eq (fun x => (ψ.commutes x).symm)
  have hrange : Set.range ψ = ↑(IsScalarTower.toAlgHom 𝒪 Onr B).range := by
    ext b; simp only [Set.mem_range, AlgHom.coe_range, IsScalarTower.coe_toAlgHom']; rfl
  have hS' : S = (Algebra.adjoin Onr (↑s : Set B)).restrictScalars 𝒪 := by
    rw [hS, hrange, ← Algebra.restrictScalars_adjoin, IsScalarTower.adjoin_range_toAlgHom]
  haveI : Algebra.FiniteType Onr ↥(Algebra.adjoin Onr (↑s : Set B)) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
  have h1 : IsNoetherianRing ↥(Algebra.adjoin Onr (↑s : Set B)) := Algebra.FiniteType.isNoetherianRing Onr _
  have h2 : IsNoetherianRing ↥((Algebra.adjoin Onr (↑s : Set B)).restrictScalars 𝒪) := h1
  exact isNoetherianRing_of_ringEquiv _ (Subalgebra.equivOfEq _ _ hS'.symm).toRingEquiv

end ASM21.SRC

theorem solution
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :

    (∀ x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      ∃ (s : Finset B) (S : Subalgebra 𝒪 B) (_ : S = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑s : Set B)))
        (x₀ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S), (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val x₀ = x) ∧

    (∀ (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (s₁ s₂ : Finset B) (S₁ S₂ : Subalgebra 𝒪 B),
      S₁ = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑s₁ : Set B)) →
      S₂ = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑s₂ : Set B)) →
      ∀ (x₁ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S₁) (x₂ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S₂),
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S₁.val x₁ = x → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S₂.val x₂ = x →
      ∃ (s₃ : Finset B) (S₃ : Subalgebra 𝒪 B) (_ : S₃ = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B from x.1) ∪ (↑s₃ : Set B)))
        (h₁ : S₁ ≤ S₃) (h₂ : S₂ ≤ S₃),
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h₁) x₁ = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h₂) x₂) ∧

    (∀ (ψ : Onr →ₐ[𝒪] B) (s : Finset B) (S : Subalgebra 𝒪 B),
      S = Algebra.adjoin 𝒪 (Set.range ψ ∪ (↑s : Set B)) → IsNoetherianRing ↥S) := by
  exact ⟨ASM21.SRC.part1 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B hB,
    ASM21.SRC.part2 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B hB,
    ASM21.SRC.part3 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B hB⟩

end S_CerednikDrinfeld_FormalOmega_exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible (solution)
