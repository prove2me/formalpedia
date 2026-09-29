-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fccbdde2-ccf3-51cc-b149-bce87ba28fa9

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_MvPowerSeries_finite_free_finrank_quotient_span_eq_of_isArtinianRing_of_finite_map
import Theorems.Thm_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_eq_mul
import Theorems.Thm_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

noncomputable section

namespace R4RigDef

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable {p : ℕ} [Fact p.Prime]

section homs

variable {A : Type u} [CommRing A] {A' : Type v} [CommRing A']

theorem cc_map {φ : Series A} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : A →+* A') (i : Fin 2) :
    constantCoeff ((φ.map f) i) = 0 := by
  show constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ i, map_zero]

theorem cc_id (i : Fin 2) : constantCoeff (Series.id A i) = 0 := constantCoeff_X _

theorem cc_act (X : FormalODModule p A) (a : Zp2 p) (i : Fin 2) : constantCoeff (X.act a i) = 0 :=
  (X.isLawHom_act a).1 i

variable {X Y Z : FormalODModule p A}

theorem hom_cc (f : X.Hom Y) (i : Fin 2) : constantCoeff (f.toSeries i) = 0 :=
  f.isODHom.constantCoeff i

@[scoped simp] theorem comp_toSeries (g : Y.Hom Z) (f : X.Hom Y) :
    (g.comp f).toSeries = g.toSeries.comp f.toSeries := rfl

@[scoped simp] theorem map_toSeries (r : A →+* A') (f : X.Hom Y) :
    (f.map r).toSeries = f.toSeries.map r := rfl

@[scoped simp] theorem id_toSeries : (FormalODModule.Hom.id X).toSeries = Series.id A := rfl

theorem inverse_unique {s g₁ g₂ : Series A} (hs : ∀ i, constantCoeff (s i) = 0)
    (hg₂ : ∀ i, constantCoeff (g₂ i) = 0)
    (h₁ : g₁.comp s = Series.id A) (h₂ : s.comp g₂ = Series.id A) : g₁ = g₂ := by
  calc g₁ = g₁.comp (Series.id A) := (Series.comp_id _).symm
    _ = g₁.comp (s.comp g₂) := by rw [h₂]
    _ = (g₁.comp s).comp g₂ := (Series.comp_assoc _ _ _ hs hg₂).symm
    _ = g₂ := by rw [h₁, Series.id_comp _ hg₂]

theorem exists_inv {f : X.Hom Y} (hf : f.IsIso) :
    ∃ g : Y.Hom X, g.toSeries.comp f.toSeries = Series.id A ∧ f.toSeries.comp g.toSeries = Series.id A := by
  obtain ⟨g, h1, h2⟩ := hf
  exact ⟨g, by simpa using congrArg FormalODModule.Hom.toSeries h1,
    by simpa using congrArg FormalODModule.Hom.toSeries h2⟩

theorem isIso_of_inv (f : X.Hom Y) (g : Y.Hom X) (h1 : g.toSeries.comp f.toSeries = Series.id A)
    (h2 : f.toSeries.comp g.toSeries = Series.id A) : f.IsIso :=
  ⟨g, FormalODModule.Hom.ext h1, FormalODModule.Hom.ext h2⟩

theorem odhom_comm_pow {φ : Series A} (h : IsODHom X Y φ) (a : ℕ) :
    (Y.act ((p : Zp2 p) ^ a)).comp φ = φ.comp (X.act ((p : Zp2 p) ^ a)) :=
  (h.2.1 _).symm

theorem act_act_comp (Y : FormalODModule p A) (a b : ℕ) (ψ : Series A) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    (Y.act ((p : Zp2 p) ^ a)).comp ((Y.act ((p : Zp2 p) ^ b)).comp ψ) =
      (Y.act ((p : Zp2 p) ^ (a + b))).comp ψ := by
  rw [← Series.comp_assoc _ _ _ (cc_act Y _) hψ, ← act_pow_add]

theorem act_odhom_comp {φ : Series A} (h : IsODHom X Y φ) (a : ℕ) (ψ : Series A)
    (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    (Y.act ((p : Zp2 p) ^ a)).comp (φ.comp ψ) = φ.comp ((X.act ((p : Zp2 p) ^ a)).comp ψ) := by
  rw [← Series.comp_assoc _ _ _ h.constantCoeff hψ, odhom_comm_pow h,
    Series.comp_assoc _ _ _ (cc_act X _) hψ]

end homs

section thick

variable {k : Type u} [Field k] [CharP k p]
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
variable (res : A →+* k) (hres : Function.Surjective res)

include hres in
theorem ker_res_eq : RingHom.ker res = IsLocalRing.maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective res hres)

include hres in

theorem exists_ker_pow_eq_bot : ∃ N : ℕ, RingHom.ker res ^ (N + 1) = ⊥ := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨N, ?_⟩
  rw [ker_res_eq res hres, ← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ N)).trans (le_of_eq hN))

include hres in
theorem isNilpotent_of_mem_ker {x : A} (hx : x ∈ RingHom.ker res) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := exists_ker_pow_eq_bot res hres
  exact ⟨N + 1, by
    have : x ^ (N + 1) ∈ RingHom.ker res ^ (N + 1) := Ideal.pow_mem_pow hx _
    rw [hN] at this
    exact (Submodule.mem_bot A).mp this⟩

theorem res_natCast_p : res (p : A) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

include hres in
theorem isNilpotent_p : IsNilpotent (p : A) :=
  isNilpotent_of_mem_ker res hres (by rw [RingHom.mem_ker, res_natCast_p])

def πk : A ⧸ pIdeal p A →+* k :=
  Ideal.Quotient.lift (pIdeal p A) res (fun a ha => by
    rw [pIdeal, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, res_natCast_p, zero_mul])

@[scoped simp] theorem πk_mk (a : A) : πk res (Ideal.Quotient.mk (pIdeal p A) a) = res a :=
  Ideal.Quotient.lift_mk _ _ _

theorem πk_comp_mk : (πk res).comp (Ideal.Quotient.mk (pIdeal p A)) = res :=
  RingHom.ext fun a => πk_mk res a

include hres in
theorem πk_surjective : Function.Surjective (πk (p := p) res) := fun x => by
  obtain ⟨a, rfl⟩ := hres x
  exact ⟨Ideal.Quotient.mk _ a, πk_mk res a⟩

def ek : k ⧸ pIdeal p k →+* k :=
  Ideal.Quotient.lift (pIdeal p k) (RingHom.id k) (fun a ha => by
    rw [pIdeal, Ideal.mem_span_singleton, CharP.cast_eq_zero] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [zero_mul, map_zero])

@[scoped simp] theorem ek_mk (a : k) : ek (p := p) (Ideal.Quotient.mk (pIdeal p k) a) = a :=
  Ideal.Quotient.lift_mk _ _ _

theorem ek_comp_mk : (ek (p := p) (k := k)).comp (Ideal.Quotient.mk (pIdeal p k)) = RingHom.id k :=
  RingHom.ext fun a => ek_mk a

theorem ek_injective : Function.Injective (ek (p := p) (k := k)) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [ek_mk, ek_mk] at h
  rw [h]

theorem ek_comp_reduceMap : (ek (p := p)).comp (reduceMap (p := p) res) = πk res := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  show ek (reduceMap res (Ideal.Quotient.mk _ a)) = πk res (Ideal.Quotient.mk _ a)
  rw [reduceMap, residueMap, Ideal.quotientMap_mk, ek_mk, πk_mk]

theorem reduceMap_comp_mk : (reduceMap (p := p) res).comp (Ideal.Quotient.mk (pIdeal p A)) =
    (Ideal.Quotient.mk (pIdeal p k)).comp res := by
  ext a
  show reduceMap res (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (res a)
  rw [reduceMap, residueMap, Ideal.quotientMap_mk]

include hres in
theorem reduceMap_surjective : Function.Surjective (reduceMap (p := p) res) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, rfl⟩ := hres x
  exact ⟨Ideal.Quotient.mk _ a, by rw [reduceMap, residueMap, Ideal.quotientMap_mk]⟩

include hres in

theorem exists_ker_reduceMap_pow_eq_bot :
    ∃ μ : ℕ, RingHom.ker (reduceMap (p := p) res) ^ (μ + 1) = ⊥ := by
  obtain ⟨N, hN⟩ := exists_ker_pow_eq_bot res hres
  refine ⟨N, ?_⟩
  have hker : RingHom.ker (reduceMap (p := p) res) = (RingHom.ker res).map (Ideal.Quotient.mk (pIdeal p A)) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hx' : Ideal.Quotient.mk (pIdeal p k) (res a) = 0 := by
        rw [RingHom.mem_ker, reduceMap, residueMap, Ideal.quotientMap_mk] at hx
        exact hx
      rw [Ideal.Quotient.eq_zero_iff_mem, pIdeal, Ideal.mem_span_singleton, CharP.cast_eq_zero] at hx'
      obtain ⟨c, hc⟩ := hx'
      rw [zero_mul] at hc
      exact Ideal.mem_map_of_mem _ (by rw [RingHom.mem_ker]; exact hc)
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, reduceMap, residueMap, Ideal.quotientMap_mk,
        RingHom.mem_ker.mp ha, map_zero]
  rw [hker, ← Ideal.map_pow, hN, Ideal.map_bot]

theorem p_pow_one_eq_zero : ((p : A ⧸ pIdeal p A)) ^ 1 = 0 := by
  rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal p A)), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

include res in

theorem nontrivial_quot : Nontrivial (A ⧸ pIdeal p A) := by
  refine Ideal.Quotient.nontrivial_iff.mpr ?_
  intro h
  have : (1 : A) ∈ pIdeal p A := h ▸ Submodule.mem_top
  rw [pIdeal, Ideal.mem_span_singleton] at this
  obtain ⟨c, hc⟩ := this
  have := congrArg res hc
  rw [map_one, map_mul, res_natCast_p, zero_mul] at this
  exact one_ne_zero this

scoped instance isArtinianRing_quot : IsArtinianRing (A ⧸ pIdeal p A) := inferInstance

include res in
theorem isLocalRing_quot : IsLocalRing (A ⧸ pIdeal p A) :=
  haveI := nontrivial_quot (p := p) res
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (pIdeal p A)) Ideal.Quotient.mk_surjective

include hres in

theorem exists_eq_comp_πk (κ : Type u) [Field κ] (f : A ⧸ pIdeal p A →+* κ) :
    ∃ g : k →+* κ, f = g.comp (πk res) := by
  have hle : RingHom.ker (πk (p := p) res) ≤ RingHom.ker f := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, πk_mk] at hx
    have hn : IsNilpotent (Ideal.Quotient.mk (pIdeal p A) a) :=
      (isNilpotent_of_mem_ker res hres (by rwa [RingHom.mem_ker])).map _
    rw [RingHom.mem_ker]
    exact (hn.map f).eq_zero
  refine ⟨(πk res).liftOfSurjective (πk_surjective res hres) ⟨f, hle⟩, ?_⟩
  exact ((πk res).liftOfSurjective_comp (πk_surjective res hres) ⟨f, hle⟩).symm

theorem exists_lift {R S : Type u} [CommRing R] [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)
    (g : Series S) (hg : ∀ i, constantCoeff (g i) = 0) :
    ∃ φ : Series R, (∀ i, constantCoeff (φ i) = 0) ∧ φ.map π = g := by
  classical
  refine ⟨fun i n => if n = 0 then 0 else Function.surjInv hπ (g i n), fun i => ?_, ?_⟩
  · show (fun n => if n = 0 then 0 else Function.surjInv hπ (g i n)) 0 = 0
    simp
  · funext i
    ext n
    show coeff n (MvPowerSeries.map π _) = coeff n (g i)
    rw [MvPowerSeries.coeff_map]
    by_cases hn : n = 0
    · subst hn
      show π ((fun n => if n = 0 then 0 else Function.surjInv hπ (g i n)) 0) = _
      simp only [if_true, map_zero]
      exact (hg i).symm
    · show π ((fun n => if n = 0 then 0 else Function.surjInv hπ (g i n)) n) = _
      simp only [hn, if_false]
      exact Function.surjInv_eq hπ _

end thick

section field

variable {κ : Type u} [Field κ]

theorem finrank_kerAlgebra_iso (u u' : Series κ) (hu : ∀ i, constantCoeff (u i) = 0)
    (hu' : ∀ i, constantCoeff (u' i) = 0) (h : u'.comp u = Series.id κ) :
    Module.finrank κ (KerAlgebra u) = 1 := by
  have hI : Ideal.span (Set.range u) = RingHom.ker (constantCoeff : MvPowerSeries (Fin 2) κ →+* κ) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (RingHom.mem_ker).mpr (hu i)
    · rw [← MvPowerSeries.span_range_X_eq_ker_constantCoeff 2, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hX : (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) = subst u (u' i) := by
        have := congrFun h i
        exact this.symm
      have hmem : u' i ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) κ)) := by
        rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff 2]
        exact (RingHom.mem_ker).mpr (hu' i)
      have hle : Ideal.map (MvPowerSeries.substAlgHom (hasSubst_of_constantCoeff_zero hu))
          (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) κ))) ≤
          Ideal.span (Set.range u) := by
        rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, MvPowerSeries.substAlgHom_apply,
          subst_X (hasSubst_of_constantCoeff_zero hu)]
        exact Ideal.subset_span ⟨j, rfl⟩
      rw [SetLike.mem_coe, hX, ← MvPowerSeries.substAlgHom_apply (hasSubst_of_constantCoeff_zero hu)]
      exact hle (Ideal.mem_map_of_mem _ hmem)
  have h1 : (Ideal.Quotient.mk (Ideal.span (Set.range u)) 1 : KerAlgebra u) ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, RingHom.mem_ker, map_one] at h0
    exact one_ne_zero h0
  refine finrank_eq_one _ h1 fun w => ?_
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨constantCoeff f, ?_⟩
  have hs : constantCoeff f • (Ideal.Quotient.mk (Ideal.span (Set.range u)) 1 : KerAlgebra u) =
      Ideal.Quotient.mk (Ideal.span (Set.range u)) (constantCoeff f • (1 : MvPowerSeries (Fin 2) κ)) := by
    exact (map_smul (Ideal.Quotient.mkₐ κ (Ideal.span (Set.range u))) (constantCoeff f) 1).symm
  rw [hs, MvPowerSeries.smul_eq_C_mul, mul_one, Ideal.Quotient.eq, hI, RingHom.mem_ker, map_sub,
    MvPowerSeries.constantCoeff_C, sub_self]

theorem finite_of_finrank_eq {V : Type*} [AddCommGroup V] [Module κ V] {d : ℕ} (hd : d ≠ 0)
    (h : Module.finrank κ V = d) : Module.Finite κ V :=
  Module.finite_of_finrank_pos (by rw [h]; exact Nat.pos_of_ne_zero hd)

theorem finrank_kerAlgebra_act_pow (Y : FormalODModule p κ)
    (hY : Module.finrank κ (KerAlgebra (Y.act (p : Zp2 p))) = p ^ 4) (μ : ℕ) :
    Module.finrank κ (KerAlgebra (Y.act ((p : Zp2 p) ^ μ))) = p ^ (μ * 4) := by
  have e1 : Y.act ((p : Zp2 p) ^ μ) = Y.F.nthSeries (p ^ μ) := by
    rw [← Nat.cast_pow]; exact Y.act_natCast _
  have e0 : Y.act (p : Zp2 p) = Y.F.nthSeries p := Y.act_natCast _
  rw [e1]
  rw [e0] at hY
  exact MvFormalGroup.finrank_quotient_span_nthSeries_pow_eq_pow p Y.F 4 hY μ

theorem finite_and_finrank_kerAlgebra_comp (f g : Series κ) (hf : ∀ i, constantCoeff (f i) = 0)
    (hg : ∀ i, constantCoeff (g i) = 0) (hffin : Module.Finite κ (KerAlgebra f))
    (hgfin : Module.Finite κ (KerAlgebra g)) :
    Module.Finite κ (KerAlgebra (f.comp g)) ∧
      Module.finrank κ (KerAlgebra (f.comp g)) = Module.finrank κ (KerAlgebra f) * Module.finrank κ (KerAlgebra g) :=
  MvPowerSeries.finite_and_finrank_quotient_span_range_subst_eq_mul f g hf hg hffin hgfin

end field

section artin

variable {k : Type u} [Field k]
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R] (π : R →+* k) (hπ : Function.Surjective π)

include hπ in

theorem hasKernelOfDegree_of_residue
    (hfac : ∀ (κ : Type u) [Field κ] (f : R →+* κ), ∃ g : k →+* κ, f = g.comp π)
    (ρ : Series R) (hρ : ∀ i, constantCoeff (ρ i) = 0) (d : ℕ) (hd : d ≠ 0)
    (H : ∀ (κ : Type u) [Field κ] (g : k →+* κ), Module.finrank κ (KerAlgebra ((ρ.map π).map g)) = d) :
    HasKernelOfDegree ρ d := by
  have hk : Module.finrank k (KerAlgebra (ρ.map π)) = d := by
    have := H k (RingHom.id k)
    rwa [Series.map_ringHom_id] at this
  have hfin : Module.Finite k (KerAlgebra (ρ.map π)) := finite_of_finrank_eq hd hk
  obtain ⟨hF, hFree, -⟩ :=
    MvPowerSeries.finite_free_finrank_quotient_span_eq_of_isArtinianRing_of_finite_map π hπ ρ hρ hfin
  refine ⟨hF, Module.Projective.of_free, fun κ _ f => ?_⟩
  obtain ⟨g, rfl⟩ := hfac κ f
  rw [← Series.map_map]
  exact H κ g

end artin

section main

variable {O : Type v} [CommRing O] (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
variable {k : Type u} [Field k] [CharP k p] (ψk : O →+* k)
variable (t₀ : Rigidified p Φ k)
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A] (ψA : O →+* A)
variable (res : A →+* k)

local notation "mkA" => Ideal.Quotient.mk (pIdeal p A)
local notation "mkk" => Ideal.Quotient.mk (pIdeal p k)
local notation "πr" => reduceMap (p := p) res

theorem Φbar_red (hψ : res.comp ψA = ψk) :
    (Φ.map (residueMap ψA)).map πr = Φ.map (residueMap ψk) := by
  rw [FormalODModule.map_map, ← residueMap_comp, hψ]

theorem Xbar_red (X : FormalODModule p A) : (X.map mkA).map πr = (X.map res).map mkk := by
  rw [FormalODModule.map_map, FormalODModule.map_map, reduceMap_comp_mk]

theorem series_red (φ : Series A) : (φ.map mkA).map πr = (φ.map res).map mkk := by
  rw [Series.map_map, Series.map_map, reduceMap_comp_mk]

variable {ι Φ ψk t₀ ψA res}

theorem cc_ρ₀ (ht₀ : t₀.IsAdmissible ι ψk) (i : Fin 2) : constantCoeff (t₀.ρ i) = 0 :=
  ht₀.constantCoeff_ρ i

theorem cc_tρ {t : Rigidified p Φ A} (ht : t.IsAdmissible ι ψA) (i : Fin 2) : constantCoeff (t.ρ i) = 0 :=
  ht.constantCoeff_ρ i

theorem finrank_lift_fibre (ht₀ : t₀.IsAdmissible ι ψk) {κ : Type u} [Field κ]
    (Y : FormalODModule p κ) (hY : Module.finrank κ (KerAlgebra (Y.act (p : Zp2 p))) = p ^ 4)
    (w wi : Series κ) (hw : ∀ i, constantCoeff (w i) = 0) (hwi : ∀ i, constantCoeff (wi i) = 0)
    (hwiw : wi.comp w = Series.id κ) (gk : k ⧸ pIdeal p k →+* κ) (μ : ℕ) :
    Module.finrank κ (KerAlgebra (((Y.act ((p : Zp2 p) ^ μ)).comp w).comp (t₀.ρ.map gk))) =
      p ^ (4 * (t₀.n + μ)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have d1 : Module.finrank κ (KerAlgebra (Y.act ((p : Zp2 p) ^ μ))) = p ^ (μ * 4) :=
    finrank_kerAlgebra_act_pow Y hY μ
  have f1 : Module.Finite κ (KerAlgebra (Y.act ((p : Zp2 p) ^ μ))) := finite_of_finrank_eq (pow_ne_zero _ hp) d1
  have d2 : Module.finrank κ (KerAlgebra w) = 1 := finrank_kerAlgebra_iso w wi hw hwi hwiw
  have f2 : Module.Finite κ (KerAlgebra w) := finite_of_finrank_eq one_ne_zero d2
  have d3 : Module.finrank κ (KerAlgebra (t₀.ρ.map gk)) = p ^ (4 * t₀.n) := ht₀.2.2.2.2.2 κ gk
  have f3 : Module.Finite κ (KerAlgebra (t₀.ρ.map gk)) := finite_of_finrank_eq (pow_ne_zero _ hp) d3
  obtain ⟨f12, d12⟩ := finite_and_finrank_kerAlgebra_comp _ w (cc_act Y _) hw f1 f2
  obtain ⟨-, d123⟩ := finite_and_finrank_kerAlgebra_comp _ (t₀.ρ.map gk)
    (Series.constantCoeff_comp (cc_act Y _) hw) (cc_map (cc_ρ₀ ht₀) gk) f12 f3
  rw [d123, d12, d1, d2, d3]
  ring

private theorem _root_.R4RigDef.lift (ht₀ : t₀.IsAdmissible ι ψk) (hres : Function.Surjective res) (hψ : res.comp ψA = ψk)
    (X : FormalODModule p A) (hXs : X.IsSpecial (ψA.comp ι)) (hXh : X.HasHeight 4)
    (v : t₀.X.Hom (X.map res)) (hv : v.IsIso) :
    ∃ (n : ℕ) (ρ : Series (A ⧸ pIdeal p A)),
      (⟨X, n, ρ⟩ : Rigidified p Φ A).IsAdmissible ι ψA ∧
      ∃ m : ℕ,
        (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).Xbar.act ((p : Zp2 p) ^ (m + n))).comp
            ((v.toSeries.map mkk).comp t₀.ρ) =
          (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp
            (((⟨X, n, ρ⟩ : Rigidified p Φ A).map res).ρ) := by
  obtain ⟨μ, hμ⟩ := exists_ker_reduceMap_pow_eq_bot (p := p) res hres

  set g : Series (k ⧸ pIdeal p k) := (v.toSeries.map mkk).comp t₀.ρ with hg
  have hvb : IsODHom (t₀.X.map mkk) ((X.map res).map mkk) (v.toSeries.map mkk) := v.isODHom.map _
  have hg_od : IsODHom (Φ.map (residueMap ψk)) ((X.map res).map mkk) g := hvb.comp ht₀.2.2.1
  have hg0 : ∀ i, constantCoeff (g i) = 0 := hg_od.constantCoeff
  obtain ⟨φ, hφ0, hφπ⟩ := exists_lift πr (reduceMap_surjective res hres) g hg0

  obtain ⟨-, hex⟩ := CerednikDrinfeld.FormalODModule.act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
    p πr μ hμ 1 (p_pow_one_eq_zero) (Φ.map (residueMap ψA)) (X.map mkA)
  have hρod := hex φ hφ0 (by rw [Φbar_red Φ ψk ψA res hψ, Xbar_red, hφπ]; exact hg_od)
  rw [one_mul] at hρod
  set ρ : Series (A ⧸ pIdeal p A) := ((X.map mkA).act ((p : Zp2 p) ^ μ)).comp φ with hρdef
  have hρ0 : ∀ i, constantCoeff (ρ i) = 0 := Series.constantCoeff_comp (cc_act _ _) hφ0

  have hρπ : ρ.map πr = (((X.map res).map mkk).act ((p : Zp2 p) ^ μ)).comp g := by
    rw [hρdef, Series.map_comp _ _ _ hφ0, hφπ, ← FormalODModule.map_act, Xbar_red]
  refine ⟨t₀.n + μ, ρ, ⟨hXs, hXh, hρod, ?_⟩, 0, ?_⟩
  ·
    haveI := isLocalRing_quot (p := p) res
    refine hasKernelOfDegree_of_residue (πk res) (πk_surjective res hres) (exists_eq_comp_πk res hres)
      ρ hρ0 _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) fun κ _ gκ => ?_
    obtain ⟨vi, hvi1, hvi2⟩ := exists_inv hv
    have hgk : (gκ.comp ek).comp mkk = gκ := by
      rw [RingHom.comp_assoc, ek_comp_mk, RingHom.comp_id]
    have hρκ : (ρ.map (πk res)).map gκ =
        ((((X.map (gκ.comp res)).act ((p : Zp2 p) ^ μ)).comp (v.toSeries.map gκ)).comp
          (t₀.ρ.map (gκ.comp ek))) := by
      rw [← ek_comp_reduceMap, ← Series.map_map, hρπ, Series.map_comp _ _ _ hg0,
        Series.map_comp _ _ _ (cc_map hg0 _), Series.map_map, Series.map_map,
        ← FormalODModule.map_act, FormalODModule.map_map, FormalODModule.map_map, hgk,
        hg, Series.map_comp _ _ _ (cc_ρ₀ ht₀), Series.map_map, hgk,
        ← Series.comp_assoc _ _ _ (cc_map (hom_cc v) _) (cc_map (cc_ρ₀ ht₀) _)]
    rw [hρκ]
    have hY : Module.finrank κ (KerAlgebra ((X.map (gκ.comp res)).act (p : Zp2 p))) = p ^ 4 :=
      hXh.2.2 κ (gκ.comp res)
    exact finrank_lift_fibre ht₀ _ hY _ _ (cc_map (hom_cc v) _) (cc_map (hom_cc vi) _)
      (by rw [← Series.map_comp _ _ _ (hom_cc v), hvi1, Series.map_id]) _ μ
  ·
    show ((((X.map res).map mkk).act ((p : Zp2 p) ^ (0 + (t₀.n + μ)))).comp g) =
      (((X.map res).map mkk).act ((p : Zp2 p) ^ (0 + t₀.n))).comp (ρ.map πr)
    rw [hρπ, act_act_comp _ _ _ _ hg0, zero_add, zero_add]

p2m_export "R4RigDef" "lift"

omit [IsLocalRing A] [IsArtinianRing A] in
theorem isNilpotent_p_field : IsNilpotent (p : k) := ⟨1, by rw [pow_one, CharP.cast_eq_zero]⟩

theorem red_eq (t t' : Rigidified p Φ A) (hρ : ∀ i, constantCoeff (t.ρ i) = 0)
    (hρ' : ∀ i, constantCoeff (t'.ρ i) = 0) (u : Series A) (hu0 : ∀ i, constantCoeff (u i) = 0) (a b : ℕ)
    (heq : (t'.Xbar.act ((p : Zp2 p) ^ a)).comp ((u.map mkA).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ b)).comp t'.ρ) :
    (((t'.X.map res).map mkk).act ((p : Zp2 p) ^ a)).comp
        (((u.map res).map mkk).comp (t.ρ.map πr)) =
      (((t'.X.map res).map mkk).act ((p : Zp2 p) ^ b)).comp (t'.ρ.map πr) := by
  have h := congrArg (Series.map πr) heq
  rw [Series.map_comp _ _ _ (Series.constantCoeff_comp (cc_map hu0 _) hρ),
    Series.map_comp _ _ _ hρ, Series.map_comp _ _ _ hρ',
    ← FormalODModule.map_act, ← FormalODModule.map_act, Xbar_red, series_red] at h
  exact h

theorem iff_clause (ht₀ : t₀.IsAdmissible ι ψk) (hres : Function.Surjective res) (hψ : res.comp ψA = ψk)
    (t t' : Rigidified p Φ A) (ht : t.IsAdmissible ι ψA) (ht' : t'.IsAdmissible ι ψA)
    (v : t₀.X.Hom (t.X.map res)) (v' : t₀.X.Hom (t'.X.map res))
    (hR : ∃ m : ℕ,
      ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp ((v.toSeries.map mkk).comp t₀.ρ) =
        ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ)
    (hR' : ∃ m : ℕ,
      ((t'.map res).Xbar.act ((p : Zp2 p) ^ (m + t'.n))).comp ((v'.toSeries.map mkk).comp t₀.ρ) =
        ((t'.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t'.map res).ρ) :
    (t.IsIsomorphic t' ↔ ∃ s : t.X.Hom t'.X, s.IsIso ∧ (s.map res).comp v = v') := by
  obtain ⟨m, hm⟩ := hR
  obtain ⟨m', hm'⟩ := hR'
  change (((t.X.map res).map mkk).act ((p : Zp2 p) ^ (m + t.n))).comp ((v.toSeries.map mkk).comp t₀.ρ) =
    (((t.X.map res).map mkk).act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.ρ.map πr) at hm
  change (((t'.X.map res).map mkk).act ((p : Zp2 p) ^ (m' + t'.n))).comp ((v'.toSeries.map mkk).comp t₀.ρ) =
    (((t'.X.map res).map mkk).act ((p : Zp2 p) ^ (m' + t₀.n))).comp (t'.ρ.map πr) at hm'

  have c0 : ∀ i, constantCoeff (t₀.ρ i) = 0 := cc_ρ₀ ht₀
  have cρ : ∀ i, constantCoeff (t.ρ.map πr i) = 0 := cc_map (cc_tρ ht) _
  have cρ' : ∀ i, constantCoeff (t'.ρ.map πr i) = 0 := cc_map (cc_tρ ht') _
  have cv : ∀ i, constantCoeff (v.toSeries.map mkk i) = 0 := cc_map (hom_cc v) _
  have cv' : ∀ i, constantCoeff (v'.toSeries.map mkk i) = 0 := cc_map (hom_cc v') _
  have hvb : IsODHom (t₀.X.map mkk) ((t.X.map res).map mkk) (v.toSeries.map mkk) := v.isODHom.map _
  constructor
  ·
    rintro ⟨u, u', m₁, hu, hu', huu, huu', heq⟩
    let s : t.X.Hom t'.X := ⟨u, hu⟩
    have hs : s.IsIso := isIso_of_inv s ⟨u', hu'⟩ huu huu'
    refine ⟨s, hs, FormalODModule.Hom.ext ?_⟩
    show (u.map res).comp v.toSeries = v'.toSeries
    have hub : IsODHom ((t.X.map res).map mkk) ((t'.X.map res).map mkk) ((u.map res).map mkk) :=
      (hu.map res).map _
    have cu : ∀ i, constantCoeff ((u.map res).map mkk i) = 0 := hub.constantCoeff
    have Hred := red_eq (res := res) t t' (cc_tρ ht) (cc_tρ ht') u hu.constantCoeff _ _ heq

    have key : (((t'.X.map res).map mkk).act ((p : Zp2 p) ^ ((m₁ + m + t.n) + t'.n))).comp
          ((((u.map res).comp v.toSeries).map mkk).comp t₀.ρ) =
        (((t'.X.map res).map mkk).act ((p : Zp2 p) ^ ((m₁ + m + t.n) + t₀.n))).comp (t'.ρ.map πr) := by
      have e1 : m₁ + m + t.n + t'.n = (m₁ + t'.n) + (m + t.n) := by omega
      have e2 : m₁ + m + t.n + t₀.n = (m + t₀.n) + (m₁ + t.n) := by omega
      rw [e1, e2, Series.map_comp _ _ _ (hom_cc v), Series.comp_assoc _ _ _ cv c0,
        ← act_act_comp _ _ _ _ (Series.constantCoeff_comp cu (Series.constantCoeff_comp cv c0)),
        act_odhom_comp hub _ _ (Series.constantCoeff_comp cv c0), hm,
        ← act_odhom_comp hub _ _ cρ, act_act_comp _ _ _ _ (Series.constantCoeff_comp cu cρ),
        add_comm (m₁ + t'.n) (m + t₀.n),
        ← act_act_comp _ _ _ _ (Series.constantCoeff_comp cu cρ), Hred, act_act_comp _ _ _ _ cρ']
    exact CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isODHom_of_act_pow_comp_map_comp_eq
      (isNilpotent_p_field (p := p) (k := k)) ι ψk t₀ (t'.map res) ht₀ cρ' ((u.map res).comp v.toSeries) v'.toSeries
      (m₁ + m + t.n) m' ((hu.map res).comp v.isODHom) v'.isODHom key hm'
  ·
    rintro ⟨s, hs, hsv⟩
    obtain ⟨si, hsi1, hsi2⟩ := exists_inv hs
    obtain ⟨μ, hμ⟩ := exists_ker_reduceMap_pow_eq_bot (p := p) res hres
    obtain ⟨huniq, -⟩ :=
      CerednikDrinfeld.FormalODModule.act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
        p πr μ hμ 1 (p_pow_one_eq_zero) (Φ.map (residueMap ψA)) t'.Xbar
    obtain ⟨c, hc⟩ : ∃ c : ℕ, c = m + m' + t₀.n := ⟨_, rfl⟩

    have hsb : IsODHom t.Xbar t'.Xbar (s.toSeries.map mkA) := s.isODHom.map _
    have h1od : IsODHom (Φ.map (residueMap ψA)) t'.Xbar
        ((t'.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp ((s.toSeries.map mkA).comp t.ρ)) :=
      (IsODHom.act_natCast_pow _ _).comp (hsb.comp ht.2.2.1)
    have h2od : IsODHom (Φ.map (residueMap ψA)) t'.Xbar ((t'.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp t'.ρ) :=
      (IsODHom.act_natCast_pow _ _).comp ht'.2.2.1

    have hsvb : ((s.toSeries.map res).map mkk).comp (v.toSeries.map mkk) = v'.toSeries.map mkk := by
      rw [← Series.map_comp _ _ _ (hom_cc v)]
      exact congrArg (Series.map mkk) (congrArg FormalODModule.Hom.toSeries hsv)
    have hub : IsODHom ((t.X.map res).map mkk) ((t'.X.map res).map mkk) ((s.toSeries.map res).map mkk) :=
      (s.isODHom.map res).map _
    have cu : ∀ i, constantCoeff ((s.toSeries.map res).map mkk i) = 0 := hub.constantCoeff
    have hred : ((t'.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp ((s.toSeries.map mkA).comp t.ρ)).map πr =
        ((t'.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp t'.ρ).map πr := by
      rw [Series.map_comp _ _ _ (Series.constantCoeff_comp (cc_map (hom_cc s) _) (cc_tρ ht)),
        Series.map_comp _ _ _ (cc_tρ ht), Series.map_comp _ _ _ (cc_tρ ht'),
        ← FormalODModule.map_act, ← FormalODModule.map_act, Xbar_red, series_red]
      have e1 : c + t'.n = (m' + t'.n) + (m + t₀.n) := by omega
      have e2 : c + t.n = (m + t.n) + (m' + t₀.n) := by omega
      have c2 : ∀ i, constantCoeff (((v.toSeries.map mkk).comp t₀.ρ) i) = 0 := Series.constantCoeff_comp cv c0
      have c3 : ∀ i, constantCoeff ((((s.toSeries.map res).map mkk).comp ((v.toSeries.map mkk).comp t₀.ρ)) i) = 0 :=
        Series.constantCoeff_comp cu c2
      rw [e1, e2, ← act_act_comp _ _ _ _ cρ', ← hm', ← hsvb, Series.comp_assoc _ _ _ cv c0,
        act_act_comp _ _ _ _ c3, add_comm (m + t.n) (m' + t'.n), ← act_act_comp _ _ _ _ c3,
        act_odhom_comp hub _ _ c2, hm, ← act_odhom_comp hub _ _ cρ,
        act_act_comp _ _ _ _ (Series.constantCoeff_comp cu cρ)]
    have hlift0 := huniq _ _ h1od h2od hred
    rw [one_mul] at hlift0
    have hlift : (t'.Xbar.act ((p : Zp2 p) ^ ((μ + c) + t'.n))).comp ((s.toSeries.map mkA).comp t.ρ) =
        (t'.Xbar.act ((p : Zp2 p) ^ ((μ + c) + t.n))).comp t'.ρ := by
      rw [add_assoc, add_assoc,
        ← act_act_comp _ _ _ _ (Series.constantCoeff_comp (cc_map (hom_cc s) _) (cc_tρ ht)),
        ← act_act_comp _ μ (c + t.n) _ (cc_tρ ht')]
      exact hlift0
    exact ⟨s.toSeries, si.toSeries, μ + c, s.isODHom, si.isODHom, hsi1, hsi2, hlift⟩

theorem descend (t : Rigidified p Φ A) (ht : t.IsAdmissible ι ψA) (h : t₀.IsIsomorphic (t.map res)) :
    ∃ (v : t₀.X.Hom (t.X.map res)), v.IsIso ∧
      ∃ m : ℕ,
        ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp ((v.toSeries.map mkk).comp t₀.ρ) =
          ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ := by
  obtain ⟨u, u', m, hu, hu', h1, h2, heq⟩ := h
  exact ⟨⟨u, hu⟩, isIso_of_inv (X := t₀.X) (Y := t.X.map res) ⟨u, hu⟩ ⟨u', hu'⟩ h1 h2, m, heq⟩

theorem ascend (ht₀ : t₀.IsAdmissible ι ψk) (t : Rigidified p Φ A) (ht : t.IsAdmissible ι ψA)
    (v : t₀.X.Hom (t.X.map res)) (hv : v.IsIso)
    (hR : ∃ m : ℕ,
      ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp ((v.toSeries.map mkk).comp t₀.ρ) =
        ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) :
    t₀.IsIsomorphic (t.map res) ∧ (t.map res).IsIsomorphic t₀ := by
  obtain ⟨m, hm⟩ := hR
  obtain ⟨vi, hvi1, hvi2⟩ := exists_inv hv
  have h : t₀.IsIsomorphic (t.map res) := ⟨v.toSeries, vi.toSeries, m, v.isODHom, vi.isODHom, hvi1, hvi2, hm⟩
  exact ⟨h, h.symm (cc_ρ₀ ht₀) (cc_map (cc_tρ ht) _)⟩

theorem baseChange (t : Rigidified p Φ A) (ht : t.IsAdmissible ι ψA)
    (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] (ψA' : O →+* A')
    (res' : A' →+* k) (f : A →+* A') (hff : res'.comp f = res) (hfψ : f.comp ψA = ψA') :
    (t.map f).IsAdmissible ι ψA' ∧
    ∀ (v : t₀.X.Hom (t.X.map res)) (v' : t₀.X.Hom ((t.map f).X.map res')),
      v'.toSeries = v.toSeries →
      (∃ m : ℕ,
          ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t.n))).comp ((v.toSeries.map mkk).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
      ∃ m : ℕ,
        (((t.map f).map res').Xbar.act ((p : Zp2 p) ^ (m + (t.map f).n))).comp
            ((v'.toSeries.map mkk).comp t₀.ρ) =
          (((t.map f).map res').Xbar.act ((p : Zp2 p) ^ (m + t₀.n))).comp ((t.map f).map res').ρ := by
  refine ⟨?_, fun v v' hv' hR => ?_⟩
  · rw [← hfψ]
    exact CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι ψA f t ht
  · obtain ⟨m, hm⟩ := hR
    refine ⟨m, ?_⟩
    rw [← Rigidified.map_comp, hff, hv']
    exact hm

end main

end R4RigDef
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing.R4RigDef"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] (ι : CerednikDrinfeld.Zp2 p →+* O)
    (Φ : CerednikDrinfeld.FormalODModule p (O ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p O))
    {k : Type u} [Field k] [CharP k p] (ψk : O →+* k)
    (t₀ : CerednikDrinfeld.SpecialFormal.Rigidified p Φ k) (ht₀ : t₀.IsAdmissible ι ψk)
    {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A] (ψA : O →+* A)
    (res : A →+* k) (hres : Function.Surjective res) (hψ : res.comp ψA = ψk) :

    (∀ (X : CerednikDrinfeld.FormalODModule p A), X.IsSpecial (ψA.comp ι) → X.HasHeight 4 →
      ∀ (v : t₀.X.Hom (X.map res)), v.IsIso →
      ∃ (n : ℕ) (ρ : CerednikDrinfeld.SpecialFormal.Series (A ⧸ CerednikDrinfeld.SpecialFormal.pIdeal p A)),
        (⟨X, n, ρ⟩ : CerednikDrinfeld.SpecialFormal.Rigidified p Φ A).IsAdmissible ι ψA ∧
        ∃ m : ℕ,
          (((⟨X, n, ρ⟩ : CerednikDrinfeld.SpecialFormal.Rigidified p Φ A).map res).Xbar.act
                ((p : CerednikDrinfeld.Zp2 p) ^ (m + n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal p k))).comp t₀.ρ) =
            (((⟨X, n, ρ⟩ : CerednikDrinfeld.SpecialFormal.Rigidified p Φ A).map res).Xbar.act
                ((p : CerednikDrinfeld.Zp2 p) ^ (m + t₀.n))).comp
              (((⟨X, n, ρ⟩ : CerednikDrinfeld.SpecialFormal.Rigidified p Φ A).map res).ρ)) ∧

    (∀ (t t' : CerednikDrinfeld.SpecialFormal.Rigidified p Φ A), t.IsAdmissible ι ψA → t'.IsAdmissible ι ψA →
      ∀ (v : t₀.X.Hom (t.X.map res)) (v' : t₀.X.Hom (t'.X.map res)),
      (∃ m : ℕ,
          ((t.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
      (∃ m : ℕ,
          ((t'.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t'.n))).comp
              ((v'.toSeries.map (Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal p k))).comp t₀.ρ) =
            ((t'.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t₀.n))).comp (t'.map res).ρ) →
      (t.IsIsomorphic t' ↔
        ∃ s : t.X.Hom t'.X, s.IsIso ∧ (s.map res).comp v = v')) ∧

    (∀ (t : CerednikDrinfeld.SpecialFormal.Rigidified p Φ A), t.IsAdmissible ι ψA → t₀.IsIsomorphic (t.map res) →
      ∃ (v : t₀.X.Hom (t.X.map res)), v.IsIso ∧
        ∃ m : ℕ,
          ((t.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) ∧

    (∀ (t : CerednikDrinfeld.SpecialFormal.Rigidified p Φ A), t.IsAdmissible ι ψA →
      ∀ (v : t₀.X.Hom (t.X.map res)), v.IsIso →
      (∃ m : ℕ,
          ((t.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t.n))).comp
              ((v.toSeries.map (Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal p k))).comp t₀.ρ) =
            ((t.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
      t₀.IsIsomorphic (t.map res) ∧ (t.map res).IsIsomorphic t₀) ∧

    (∀ (t : CerednikDrinfeld.SpecialFormal.Rigidified p Φ A), t.IsAdmissible ι ψA →
      ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] (ψA' : O →+* A')
        (res' : A' →+* k), Function.Surjective res' → res'.comp ψA' = ψk →
      ∀ (f : A →+* A'), res'.comp f = res → f.comp ψA = ψA' →
        (t.map f).IsAdmissible ι ψA' ∧
        ∀ (v : t₀.X.Hom (t.X.map res)) (v' : t₀.X.Hom ((t.map f).X.map res')),
          v'.toSeries = v.toSeries →
          (∃ m : ℕ,
              ((t.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t.n))).comp
                  ((v.toSeries.map (Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal p k))).comp t₀.ρ) =
                ((t.map res).Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t₀.n))).comp (t.map res).ρ) →
          ∃ m : ℕ,
            (((t.map f).map res').Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + (t.map f).n))).comp
                ((v'.toSeries.map (Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal p k))).comp t₀.ρ) =
              (((t.map f).map res').Xbar.act ((p : CerednikDrinfeld.Zp2 p) ^ (m + t₀.n))).comp
                ((t.map f).map res').ρ) := by
  refine ⟨fun X hXs hXh v hv => R4RigDef.lift ht₀ hres hψ X hXs hXh v hv,
    fun t t' ht ht' v v' hR hR' => R4RigDef.iff_clause ht₀ hres hψ t t' ht ht' v v' hR hR',
    fun t ht h => R4RigDef.descend t ht h,
    fun t ht v hv hR => R4RigDef.ascend ht₀ t ht v hv hR,
    fun t ht A' _ _ _ ψA' res' hres' hψ' f hff hfψ => R4RigDef.baseChange t ht A' ψA' res' f hff hfψ⟩

end
end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isIsomorphic_iff_exists_isIso_of_isArtinianRing (solution)
