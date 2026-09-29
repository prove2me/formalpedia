-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.even_of_isIsogenyOfHeight_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d9183f60-08e5-5594-a719-145eb76ea4a7

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Theorems.Thm_MvFormalGroup_CartierModule_length_quotient_range_mapLinear_eq_of_finrank_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

noncomputable section

namespace R4Parity

section Index

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
variable {R₂ : Type*} [Ring R₂] {M₂ : Type*} [AddCommGroup M₂] [Module R₂ M₂]
variable {τ : R →+* R₂} [RingHomSurjective τ]

theorem length_eq_of_bijective (f : M →ₛₗ[τ] M₂) (hf : Function.Bijective f) :
    Module.length R M = Module.length R₂ M₂ := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem length_quotient_ker (f : M →ₛₗ[τ] M₂) :
    Module.length R (M ⧸ LinearMap.ker f) = Module.length R₂ (LinearMap.range f) := by
  have hle : LinearMap.ker f ≤ LinearMap.ker f.rangeRestrict := by
    rw [LinearMap.ker_rangeRestrict]
  refine length_eq_of_bijective ((LinearMap.ker f).liftQ f.rangeRestrict hle) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (by rw [LinearMap.ker_rangeRestrict])
  · rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict]

def idx (Z Y : Submodule R M) : ℕ∞ := Module.length R (Y ⧸ Z.comap Y.subtype)

omit [RingHomSurjective τ] in
theorem comap_subtype_eq_of_inf_eq {Z Z' Y : Submodule R M} (h : Y ⊓ Z = Y ⊓ Z') :
    Z.comap Y.subtype = Z'.comap Y.subtype := by
  ext ⟨y, hy⟩
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro hz
    have hmem : y ∈ Y ⊓ Z' := by rw [← h]; exact Submodule.mem_inf.mpr ⟨hy, hz⟩
    exact (Submodule.mem_inf.mp hmem).2
  · intro hz
    have hmem : y ∈ Y ⊓ Z := by rw [h]; exact Submodule.mem_inf.mpr ⟨hy, hz⟩
    exact (Submodule.mem_inf.mp hmem).2

omit [RingHomSurjective τ] in
theorem idx_congr {Z Z' Y : Submodule R M} (h : Y ⊓ Z = Y ⊓ Z') : idx Z Y = idx Z' Y := by
  unfold idx
  rw [comap_subtype_eq_of_inf_eq h]

theorem idx_map (f : M →ₛₗ[τ] M₂) (hf : Function.Injective f) (Z Y : Submodule R M) :
    idx (Z.map f) (Y.map f) = idx Z Y := by
  let fY : Y →ₛₗ[τ] ↥(Y.map f) :=
    (f.domRestrict Y).codRestrict (Y.map f) fun y => ⟨y, y.2, rfl⟩
  let g : Y →ₛₗ[τ] ↥(Y.map f) ⧸ (Z.map f).comap (Y.map f).subtype :=
    ((Z.map f).comap (Y.map f).subtype).mkQ.comp fY
  have hg_surj : Function.Surjective g := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hg_ker : LinearMap.ker g = Z.comap Y.subtype := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      show g ⟨y, hy⟩ = Submodule.Quotient.mk (fY ⟨y, hy⟩) from rfl,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    show f y ∈ Z.map f ↔ y ∈ Z
    constructor
    · rintro ⟨z, hz, hzy⟩
      rwa [← hf hzy]
    · intro hz
      exact ⟨y, hz, rfl⟩
  calc idx (Z.map f) (Y.map f)
      = Module.length R₂ (LinearMap.range g) := by
        rw [LinearMap.range_eq_top.mpr hg_surj, Module.length_top]; rfl
    _ = Module.length R (Y ⧸ LinearMap.ker g) := (length_quotient_ker g).symm
    _ = idx Z Y := by rw [hg_ker]; rfl

omit [RingHomSurjective τ] in

theorem idx_add {Z Y X : Submodule R M} (hZY : Z ≤ Y) (hYX : Y ≤ X) :
    idx Z X = idx Y X + idx Z Y := by
  set Z' : Submodule R X := Z.comap X.subtype with hZ'
  set Y' : Submodule R X := Y.comap X.subtype with hY'
  have hle : Z' ≤ Y' := Submodule.comap_mono hZY
  have h1 := Module.length_eq_add_of_exact (Y'.map Z'.mkQ).subtype (Y'.map Z'.mkQ).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 : Module.length R ((X ⧸ Z') ⧸ Y'.map Z'.mkQ) = idx Y X :=
    LinearEquiv.length_eq (Submodule.quotientQuotientEquivQuotient Z' Y' hle)
  have h3 : Module.length R (Y'.map Z'.mkQ) = idx Z Y := by
    let g : Y →ₗ[R] X ⧸ Z' := Z'.mkQ.comp (Submodule.inclusion hYX)
    have hrange : LinearMap.range g = Y'.map Z'.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_inclusion]
    have hker : LinearMap.ker g = Z.comap Y.subtype := by
      ext ⟨y, hy⟩
      rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
        show g ⟨y, hy⟩ = Submodule.Quotient.mk (Submodule.inclusion hYX ⟨y, hy⟩) from rfl,
        Submodule.Quotient.mk_eq_zero, hZ', Submodule.mem_comap]
      rfl
    rw [← hrange, ← length_quotient_ker g, hker]
    rfl
  rw [show idx Z X = Module.length R (X ⧸ Z') from rfl, h1, h2, h3, add_comm]

omit [RingHomSurjective τ] in

theorem idx_anti {Z Z' : Submodule R M} (h : Z' ≤ Z) (Y : Submodule R M) : idx Z Y ≤ idx Z' Y :=
  Module.length_le_of_surjective (Submodule.factor (Submodule.comap_mono (f := Y.subtype) h))
    (Submodule.factor_surjective _)

omit [RingHomSurjective τ] in

theorem idx_sup (p p' : Submodule R M) : idx p' (p ⊔ p') = idx p' p := by
  unfold idx
  rw [← LinearEquiv.length_eq (LinearMap.quotientInfEquivSupQuotient p p')]
  have h : Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype p' =
      Submodule.comap p.subtype p' := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  exact LinearEquiv.length_eq (Submodule.quotEquivOfEq _ _ h)

omit [RingHomSurjective τ] in

theorem idx_top (N : Submodule R M) : idx N ⊤ = Module.length R (M ⧸ N) := by
  let g : (⊤ : Submodule R M) →ₗ[R] M ⧸ N := N.mkQ.comp (⊤ : Submodule R M).subtype
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N q
    exact ⟨⟨x, trivial⟩, rfl⟩
  have hker : LinearMap.ker g = N.comap (⊤ : Submodule R M).subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  calc idx N ⊤ = Module.length R ((⊤ : Submodule R M) ⧸ LinearMap.ker g) := by rw [hker]; rfl
    _ = Module.length R (LinearMap.range g) := length_quotient_ker g
    _ = Module.length R (M ⧸ N) := by rw [LinearMap.range_eq_top.mpr hsurj, Module.length_top]

omit [RingHomSurjective τ] in

theorem idx_sup_top {A₀ A₁ B₀ B₁ : Submodule R M} (hA : IsCompl A₀ A₁) (h₀ : B₀ ≤ A₀)
    (h₁ : B₁ ≤ A₁) : idx (B₀ ⊔ B₁) ⊤ = idx B₀ A₀ + idx B₁ A₁ := by
  have step1 : idx (B₀ ⊔ B₁) (A₀ ⊔ B₁) = idx B₀ A₀ := by
    have hsup : A₀ ⊔ B₁ = A₀ ⊔ (B₀ ⊔ B₁) := by rw [← sup_assoc, sup_eq_left.mpr h₀]
    rw [hsup, idx_sup]
    apply idx_congr
    rw [inf_comm, sup_inf_assoc_of_le B₁ h₀, (hA.symm.disjoint.mono_left h₁).eq_bot, sup_bot_eq,
      inf_eq_right.mpr h₀]
  have step2 : idx (A₀ ⊔ B₁) ⊤ = idx B₁ A₁ := by
    have htop : (⊤ : Submodule R M) = A₁ ⊔ (A₀ ⊔ B₁) := by
      rw [← sup_assoc, hA.symm.sup_eq_top, top_sup_eq]
    rw [htop, idx_sup]
    apply idx_congr
    rw [inf_comm, sup_comm A₀ B₁, sup_inf_assoc_of_le A₀ h₁, hA.disjoint.eq_bot, sup_bot_eq,
      inf_eq_right.mpr h₁]
  calc idx (B₀ ⊔ B₁) ⊤ = idx (A₀ ⊔ B₁) ⊤ + idx (B₀ ⊔ B₁) (A₀ ⊔ B₁) :=
        idx_add (sup_le_sup_right h₀ _) le_top
    _ = idx B₁ A₁ + idx B₀ A₀ := by rw [step1, step2]
    _ = idx B₀ A₀ + idx B₁ A₁ := add_comm _ _

end Index

section Cartier

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p]
variable {j : Zp2 p →+* k}

omit [CharP k p] [PerfectRing k p] in
theorem smul_mem_gradedPiece (X : SpecialFormalODModule p j) (n : ℕ) (w : WittVector p k)
    (f : CartierModule p X.F) (hf : f ∈ X.toFormalODModule.gradedPiece j n) :
    w • f ∈ X.toFormalODModule.gradedPiece j n := by
  intro c
  have hfc := hf c
  rw [endAct_smul_witt, hfc, homothety_smul_witt]

def piece (X : SpecialFormalODModule p j) (n : ℕ) :
    Submodule (WittVector p k) (CartierModule p X.F) where
  carrier := X.toFormalODModule.gradedPiece j n
  add_mem' hf hg := (X.toFormalODModule.gradedPiece j n).add_mem hf hg
  zero_mem' := (X.toFormalODModule.gradedPiece j n).zero_mem
  smul_mem' w f hf := smul_mem_gradedPiece X n w f hf

omit [CharP k p] [PerfectRing k p] in
theorem mem_piece (X : SpecialFormalODModule p j) {n : ℕ} {f : CartierModule p X.F} :
    f ∈ piece X n ↔ f ∈ X.toFormalODModule.gradedPiece j n := Iff.rfl

omit [CharP k p] [PerfectRing k p] in
theorem piece_two (X : SpecialFormalODModule p j) : piece X 2 = piece X 0 := by
  ext f
  have h := gradedPiece_add_two X.toFormalODModule j 0
  rw [show (0 : ℕ) + 2 = 2 from rfl] at h
  rw [mem_piece, mem_piece, h]

omit [PerfectRing k p] in

theorem grading (X : SpecialFormalODModule p j) :
    IsCompl (X.toFormalODModule.gradedPiece j 0) (X.toFormalODModule.gradedPiece j 1) ∧
    (∀ (n : ℕ) (g : CartierModule p X.F),
        verschiebung g ∈ X.toFormalODModule.gradedPiece j (n + 1) ↔
          g ∈ X.toFormalODModule.gradedPiece j n) ∧
    (∀ n, ∀ f ∈ X.toFormalODModule.gradedPiece j n,
        endAct X.varpiEnd f ∈ X.toFormalODModule.gradedPiece j (n + 1)) ∧
    (X.toFormalODModule.gradedPiece j 0).map (tangent : CartierModule p X.F →+ (Fin 2 → k)) =
      (X.lieZero j).toAddSubgroup ∧
    (X.toFormalODModule.gradedPiece j 1).map (tangent : CartierModule p X.F →+ (Fin 2 → k)) =
      (X.lieOne j).toAddSubgroup := by
  obtain ⟨h1, h2, -, h4, -, -, h7, h8⟩ :=
    isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p j X.toFormalODModule X.isSpecial.1
  exact ⟨h1, h2, h4, h7, h8⟩

omit [PerfectRing k p] in

theorem isCompl_piece (X : SpecialFormalODModule p j) : IsCompl (piece X 0) (piece X 1) := by
  have h := (grading X).1
  refine isCompl_iff.mpr ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro f hf0 hf1
    exact AddSubgroup.disjoint_def.mp h.disjoint hf0 hf1
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro f
    have hsup : f ∈ X.toFormalODModule.gradedPiece j 0 ⊔ X.toFormalODModule.gradedPiece j 1 := by
      rw [codisjoint_iff.mp h.codisjoint]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hsup
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, hyz⟩

def PiL (X : SpecialFormalODModule p j) :
    CartierModule p X.F →ₗ[WittVector p k] CartierModule p X.F :=
  mapLinear X.varpiEnd

omit [CharP k p] [PerfectRing k p] in
@[scoped simp] theorem PiL_apply (X : SpecialFormalODModule p j) (f : CartierModule p X.F) :
    PiL X f = endAct X.varpiEnd f := rfl

def sigmaInv (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p] :
    WittVector p k →+* WittVector p k :=
  ((WittVector.frobeniusEquiv p k).symm : WittVector p k ≃+* WittVector p k).toRingHom

scoped instance instRingHomSurjective_sigmaInv : RingHomSurjective (sigmaInv p k) :=
  ⟨(WittVector.frobeniusEquiv p k).symm.surjective⟩

def VL (X : SpecialFormalODModule p j) :
    CartierModule p X.F →ₛₗ[sigmaInv p k] CartierModule p X.F where
  toFun := verschiebung
  map_add' := map_add _
  map_smul' w f := verschiebung_smul w f

@[scoped simp] theorem VL_apply (X : SpecialFormalODModule p j) (f : CartierModule p X.F) :
    VL X f = verschiebung f := rfl

omit [PerfectRing k p] in
theorem map_PiL_le (X : SpecialFormalODModule p j) (n : ℕ) :
    (piece X n).map (PiL X) ≤ piece X (n + 1) := by
  rintro _ ⟨f, hf, rfl⟩
  exact (grading X).2.2.1 n f hf

theorem map_VL_le (X : SpecialFormalODModule p j) (n : ℕ) :
    (piece X n).map (VL X) ≤ piece X (n + 1) := by
  rintro _ ⟨f, hf, rfl⟩
  exact ((grading X).2.1 n f).mpr hf

theorem VL_injective (X : SpecialFormalODModule p j) : Function.Injective (VL X) :=
  verschiebung_injective

theorem VL_PiL (X : SpecialFormalODModule p j) (f : CartierModule p X.F) :
    VL X (PiL X f) = PiL X (VL X f) :=
  (endAct_verschiebung X.varpiEnd f).symm

theorem map_map_VL_PiL (X : SpecialFormalODModule p j)
    (N : Submodule (WittVector p k) (CartierModule p X.F)) :
    (N.map (PiL X)).map (VL X) = (N.map (VL X)).map (PiL X) := by
  ext g
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨VL X f, ⟨f, hf, rfl⟩, (VL_PiL X f).symm⟩
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨PiL X f, ⟨f, hf, rfl⟩, VL_PiL X f⟩

omit [CharP k p] [PerfectRing k p] in

theorem finrank_kerAlgebra (X : SpecialFormalODModule p j) :
    Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X.F.nthSeries p))) =
      p ^ 4 := by
  have h := X.hasHeight.2.2 k (RingHom.id k)
  have hmap : (X.act (p : Zp2 p)).map (RingHom.id k) = X.F.nthSeries p := by
    funext i
    show MvPowerSeries.map (RingHom.id k) (X.act (p : Zp2 p) i) = X.F.nthSeries p i
    rw [MvPowerSeries.map_id, ← X.act_natCast]
    rfl
  rw [hmap] at h
  exact h

def pEnd (X : SpecialFormalODModule p j) : MvFormalGroup.End X.F :=
  ((p : ℕ) : MvFormalGroup.End X.F)

omit [CharP k p] [PerfectRing k p] in
theorem map_pEnd (X : SpecialFormalODModule p j) (f : CartierModule p X.F) :
    map (pEnd X) f = (p : WittVector p k) • f := by
  rw [natCast_smul_eq_nsmul', ← endAct_natCast]
  rfl

omit [CharP k p] [PerfectRing k p] in

theorem PiL_PiL (X : SpecialFormalODModule p j) (f : CartierModule p X.F) :
    PiL X (PiL X f) = (p : WittVector p k) • f := by
  rw [PiL_apply, PiL_apply, ← map_pEnd]
  show (endAct X.varpiEnd * endAct X.varpiEnd : AddMonoid.End (CartierModule p X.F)) f =
    endAct (pEnd X) f
  rw [← map_mul, varpiEnd_mul_varpiEnd, actRingHom, map_natCast]
  rfl

omit [CharP k p] [PerfectRing k p] in

theorem smul_p_injective (X : SpecialFormalODModule p j) :
    Function.Injective (fun f : CartierModule p X.F => (p : WittVector p k) • f) := by
  have hinj : Function.Injective (map (p := p) (pEnd X)) := by
    refine map_injective_of_finite_quotient p X.F X.F _ ?_
    rw [pEnd, MvFormalGroup.End.toPowerSeries_natCast]
    exact Module.finite_of_finrank_pos (by rw [finrank_kerAlgebra X]; exact pow_pos hp.out.pos 4)
  intro f g hfg
  apply hinj
  have h' : (p : WittVector p k) • f = (p : WittVector p k) • g := hfg
  rwa [← map_pEnd, ← map_pEnd] at h'

omit [CharP k p] [PerfectRing k p] in
theorem PiL_injective (X : SpecialFormalODModule p j) : Function.Injective (PiL X) := by
  intro f g hfg
  apply smul_p_injective X
  show (p : WittVector p k) • f = (p : WittVector p k) • g
  rw [← PiL_PiL, ← PiL_PiL, hfg]

theorem length_quotient_p (X : SpecialFormalODModule p j) :
    Module.length (WittVector p k) (CartierModule p X.F ⧸ LinearMap.range (mapLinear (pEnd X))) =
      (4 : ℕ) :=
  length_quotient_range_mapLinear_eq_of_finrank_eq_pow p X.F X.F (pEnd X) 4
    (by rw [pEnd, MvFormalGroup.End.toPowerSeries_natCast]; exact finrank_kerAlgebra X)

omit [PerfectRing k p] in

theorem range_p_le (X : SpecialFormalODModule p j) :
    LinearMap.range (mapLinear (pEnd X)) ≤ piece X 0 ⊔ (piece X 0).map (PiL X) := by
  rintro _ ⟨f, rfl⟩
  rw [mapLinear_apply, map_pEnd]
  have htop : f ∈ (⊤ : Submodule (WittVector p k) (CartierModule p X.F)) := trivial
  rw [← (isCompl_piece X).sup_eq_top] at htop
  obtain ⟨f₀, hf₀, f₁, hf₁, rfl⟩ := Submodule.mem_sup.mp htop
  rw [smul_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ hf₀))
    (Submodule.mem_sup_right ?_)
  rw [← PiL_PiL]
  refine ⟨PiL X f₁, ?_, rfl⟩
  have h2 : PiL X f₁ ∈ piece X (1 + 1) := map_PiL_le X 1 ⟨f₁, hf₁, rfl⟩
  have h2' : piece X (1 + 1) = piece X 0 := piece_two X
  rw [h2'] at h2
  exact h2

theorem idx_PiL_lt_top (X : SpecialFormalODModule p j) :
    idx ((piece X 0).map (PiL X)) (piece X 1) < ⊤ := by
  have hle : (piece X 0).map (PiL X) ≤ piece X 1 := map_PiL_le X 0
  have hsup : piece X 1 ⊔ (piece X 0 ⊔ (piece X 0).map (PiL X)) = ⊤ := by
    rw [← sup_assoc, sup_comm (piece X 1), (isCompl_piece X).sup_eq_top, top_sup_eq]
  have h1 : idx ((piece X 0).map (PiL X)) (piece X 1) =
      idx (piece X 0 ⊔ (piece X 0).map (PiL X)) ⊤ := by
    rw [← hsup, idx_sup]
    apply idx_congr
    rw [inf_eq_right.mpr hle, inf_comm, sup_comm (piece X 0), sup_inf_assoc_of_le _ hle,
      (isCompl_piece X).disjoint.eq_bot, sup_bot_eq]
  rw [h1]
  refine lt_of_le_of_lt (idx_anti (range_p_le X) _) ?_
  rw [idx_top, length_quotient_p]
  exact ENat.coe_lt_top 4

scoped instance instRingHomSurjective_constantCoeff :
    RingHomSurjective (WittVector.constantCoeff : WittVector p k →+* k) :=
  ⟨fun a => ⟨WittVector.teichmuller p a, WittVector.teichmuller_coeff_zero p a⟩⟩

def TL (X : SpecialFormalODModule p j) :
    CartierModule p X.F →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] (Fin 2 → k) where
  toFun := tangent
  map_add' := map_add _
  map_smul' w f := tangent_smul_witt w f

theorem idx_VL_eq_one (X : SpecialFormalODModule p j) (n : ℕ) (L : Submodule k (Fin 2 → k))
    (hLinv : Module.Invertible k L)
    (hL : (X.toFormalODModule.gradedPiece j (n + 1)).map
        (tangent : CartierModule p X.F →+ (Fin 2 → k)) = L.toAddSubgroup) :
    idx ((piece X n).map (VL X)) (piece X (n + 1)) = 1 := by
  let g := (TL X).domRestrict (piece X (n + 1))
  have hker : LinearMap.ker g = ((piece X n).map (VL X)).comap (piece X (n + 1)).subtype := by
    ext ⟨f, hf⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map,
      LinearMap.domRestrict_apply]
    show tangent f = 0 ↔ _
    rw [tangent_eq_zero_iff_exists_verschiebung_eq p X.F f]
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g', ((grading X).2.1 n g').mp hf, rfl⟩
    · rintro ⟨g', -, rfl⟩
      exact ⟨g', rfl⟩
  have hrange : LinearMap.range g = L := by
    ext v
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨⟨f, hf⟩, rfl⟩
      have hv : tangent f ∈ (X.toFormalODModule.gradedPiece j (n + 1)).map
          (tangent : CartierModule p X.F →+ (Fin 2 → k)) := ⟨f, hf, rfl⟩
      rw [hL] at hv
      exact hv
    · intro hv
      have hv' : v ∈ L.toAddSubgroup := hv
      rw [← hL] at hv'
      obtain ⟨f, hf, rfl⟩ := hv'
      exact ⟨⟨f, hf⟩, rfl⟩
  haveI := hLinv
  calc idx ((piece X n).map (VL X)) (piece X (n + 1))
      = Module.length (WittVector p k) (↥(piece X (n + 1)) ⧸ LinearMap.ker g) := by
        rw [hker]; rfl
    _ = Module.length k (LinearMap.range g) := length_quotient_ker g
    _ = Module.length k L := by rw [hrange]
    _ = 1 := by
      rw [Module.length_eq_finrank, Module.Invertible.finrank_eq_one k L]
      rfl

theorem idx_VL_zero (X : SpecialFormalODModule p j) :
    idx ((piece X 0).map (VL X)) (piece X 1) = 1 :=
  idx_VL_eq_one X 0 (X.lieOne j) X.isSpecial.2.2 (grading X).2.2.2.2

theorem idx_VL_one (X : SpecialFormalODModule p j) :
    idx ((piece X 1).map (VL X)) (piece X 0) = 1 := by
  have h := idx_VL_eq_one X 1 (X.lieZero j) X.isSpecial.2.1
    (by rw [gradedPiece_add_two]; exact (grading X).2.2.2.1)
  have h2 : piece X (1 + 1) = piece X 0 := piece_two X
  rw [h2] at h
  exact h

omit [PerfectRing k p] in
theorem map_PiL_one_le (X : SpecialFormalODModule p j) : (piece X 1).map (PiL X) ≤ piece X 0 := by
  have h := map_PiL_le X 1
  have h2 : piece X (1 + 1) = piece X 0 := piece_two X
  rw [h2] at h
  exact h

theorem map_VL_one_le (X : SpecialFormalODModule p j) : (piece X 1).map (VL X) ≤ piece X 0 := by
  have h := map_VL_le X 1
  have h2 : piece X (1 + 1) = piece X 0 := piece_two X
  rw [h2] at h
  exact h

theorem exists_idx_PiL_eq (X : SpecialFormalODModule p j) :
    ∃ a : ℕ, idx ((piece X 0).map (PiL X)) (piece X 1) = a ∧
      idx ((piece X 1).map (PiL X)) (piece X 0) = a := by

  have lhs : idx (((piece X 0).map (PiL X)).map (VL X)) (piece X 0) =
      1 + idx ((piece X 0).map (PiL X)) (piece X 1) := by
    rw [idx_add (Submodule.map_mono (map_PiL_le X 0)) (map_VL_one_le X),
      idx_map (VL X) (VL_injective X), idx_VL_one]

  have rhs : idx (((piece X 0).map (VL X)).map (PiL X)) (piece X 0) =
      idx ((piece X 1).map (PiL X)) (piece X 0) + 1 := by
    rw [idx_add (Submodule.map_mono (map_VL_le X 0)) (map_PiL_one_le X),
      idx_map (PiL X) (PiL_injective X), idx_VL_zero]
  have heq : 1 + idx ((piece X 0).map (PiL X)) (piece X 1) =
      idx ((piece X 1).map (PiL X)) (piece X 0) + 1 := by
    rw [← lhs, ← rhs, map_map_VL_PiL]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (idx_PiL_lt_top X).ne
  refine ⟨a, ha.symm, ?_⟩
  rw [← ha] at heq
  have hb : idx ((piece X 1).map (PiL X)) (piece X 0) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at heq
    exact WithTop.coe_ne_top (a := 1 + a) (by push_cast; exact heq)
  obtain ⟨b, hb'⟩ := WithTop.ne_top_iff_exists.mp hb
  rw [← hb'] at heq ⊢
  have hab : ((1 + a : ℕ) : ℕ∞) = ((b + 1 : ℕ) : ℕ∞) := by push_cast; exact heq
  have hab' : 1 + a = b + 1 := Nat.cast_injective hab
  congr 1
  omega

theorem main (Φ Φ' : SpecialFormalODModule p j) (ρ : SpecialFormal.Series k) (h : ℕ)
    (hρ : IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule ρ h) : Even h := by

  let ρh : MvFormalGroup.Hom Φ.F Φ'.F := hρ.1.1.toHom
  let θ : CartierModule p Φ.F →ₗ[WittVector p k] CartierModule p Φ'.F := mapLinear ρh
  have hθ_apply : ∀ f, θ f = map ρh f := fun f => rfl
  have hθinj : Function.Injective θ := map_injective_of_finite_quotient p Φ.F Φ'.F ρh hρ.2.1

  have hdeg : Module.finrank k
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range ρh.toPowerSeries)) = p ^ h := by
    have hfib := hρ.2.2.2 k (RingHom.id k)
    have hmap : ρ.map (RingHom.id k) = ρ := by
      funext i
      show MvPowerSeries.map (RingHom.id k) (ρ i) = ρ i
      rw [MvPowerSeries.map_id]
      rfl
    rw [hmap] at hfib
    exact hfib
  have hlen : Module.length (WittVector p k) (CartierModule p Φ'.F ⧸ LinearMap.range θ) = h :=
    length_quotient_range_mapLinear_eq_of_finrank_eq_pow p Φ.F Φ'.F ρh h hdeg

  have hθPi : ∀ f, θ (PiL Φ f) = PiL Φ' (θ f) := fun f => by
    rw [hθ_apply, hθ_apply, PiL_apply, PiL_apply, endAct_apply, endAct_apply,
      ← CartierModule.map_comp, ← CartierModule.map_comp,
      show ρh.comp Φ.varpiEnd = MvFormalGroup.Hom.comp Φ'.varpiEnd ρh from
        MvFormalGroup.Hom.ext hρ.1.2.2]
  have hθpiece : ∀ n, (piece Φ n).map θ ≤ piece Φ' n := fun n => by
    rintro _ ⟨f, hf, rfl⟩
    intro c
    have hfc := hf c
    rw [hθ_apply, endAct_apply, ← CartierModule.map_comp,
      show (Φ'.actEnd (WittVector.teichmuller p c)).comp ρh =
        ρh.comp (Φ.actEnd (WittVector.teichmuller p c)) from
        MvFormalGroup.Hom.ext (hρ.1.2.1 _).symm,
      CartierModule.map_comp, ← map_homothety]
    exact congrArg (CartierModule.map ρh) hfc
  have hcomm : ∀ N : Submodule (WittVector p k) (CartierModule p Φ.F),
      (N.map (PiL Φ)).map θ = (N.map θ).map (PiL Φ') := fun N => by
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    exact LinearMap.ext fun f => hθPi f

  obtain ⟨a, ha, hb⟩ := exists_idx_PiL_eq Φ
  obtain ⟨a', ha', hb'⟩ := exists_idx_PiL_eq Φ'
  set ℓ₀ := idx ((piece Φ 0).map θ) (piece Φ' 0) with hℓ₀
  set ℓ₁ := idx ((piece Φ 1).map θ) (piece Φ' 1) with hℓ₁

  have hsum : ℓ₀ + ℓ₁ = h := by
    rw [← hlen, ← idx_top]
    have hrange : LinearMap.range θ = (piece Φ 0).map θ ⊔ (piece Φ 1).map θ := by
      rw [← Submodule.map_sup, (isCompl_piece Φ).sup_eq_top, Submodule.map_top]
    rw [hrange, idx_sup_top (isCompl_piece Φ') (hθpiece 0) (hθpiece 1)]

  have E1 : ℓ₁ + a = a' + ℓ₀ := by
    have lhs : idx (((piece Φ 0).map (PiL Φ)).map θ) (piece Φ' 1) = ℓ₁ + a := by
      rw [idx_add (Submodule.map_mono (map_PiL_le Φ 0)) (hθpiece 1), idx_map θ hθinj, ha]
    have rhs : idx (((piece Φ 0).map θ).map (PiL Φ')) (piece Φ' 1) = a' + ℓ₀ := by
      rw [idx_add (Submodule.map_mono (hθpiece 0)) (map_PiL_le Φ' 0),
        idx_map (PiL Φ') (PiL_injective Φ'), ha']
    rw [← lhs, hcomm, rhs]

  have E2 : ℓ₀ + a = a' + ℓ₁ := by
    have lhs : idx (((piece Φ 1).map (PiL Φ)).map θ) (piece Φ' 0) = ℓ₀ + a := by
      rw [idx_add (Submodule.map_mono (map_PiL_one_le Φ)) (hθpiece 0), idx_map θ hθinj, hb]
    have rhs : idx (((piece Φ 1).map θ).map (PiL Φ')) (piece Φ' 0) = a' + ℓ₁ := by
      rw [idx_add (Submodule.map_mono (hθpiece 1)) (map_PiL_one_le Φ'),
        idx_map (PiL Φ') (PiL_injective Φ'), hb']
    rw [← lhs, hcomm, rhs]

  have hℓ₀fin : ℓ₀ ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hsum
    exact WithTop.coe_ne_top hsum.symm
  have hℓ₁fin : ℓ₁ ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hsum
    exact WithTop.coe_ne_top hsum.symm
  obtain ⟨l₀, hl₀⟩ := WithTop.ne_top_iff_exists.mp hℓ₀fin
  obtain ⟨l₁, hl₁⟩ := WithTop.ne_top_iff_exists.mp hℓ₁fin
  rw [← hl₀, ← hl₁] at hsum E1 E2
  have hsum' : l₀ + l₁ = h :=
    Nat.cast_injective (R := ℕ∞) (by push_cast; exact hsum)
  have E1' : l₁ + a = a' + l₀ :=
    Nat.cast_injective (R := ℕ∞) (by push_cast; exact E1)
  have E2' : l₀ + a = a' + l₁ :=
    Nat.cast_injective (R := ℕ∞) (by push_cast; exact E2)
  exact ⟨l₀, by omega⟩

end Cartier

end R4Parity
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed.R4Parity"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed.R4Parity"

open R4Parity in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j)
    (ρ : CerednikDrinfeld.SpecialFormal.Series k) (h : ℕ)
    (hρ : CerednikDrinfeld.FormalODModule.IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule ρ h) :
    Even h :=
  R4Parity.main Φ Φ' ρ h hρ

end S_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed (solution)
