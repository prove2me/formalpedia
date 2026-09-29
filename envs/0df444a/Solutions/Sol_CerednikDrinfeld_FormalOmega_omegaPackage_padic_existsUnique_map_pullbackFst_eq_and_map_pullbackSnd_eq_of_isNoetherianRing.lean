-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/258e7ff1-11fd-55d3-83c2-f581f4687e11

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_OmegaModuliPackage
import Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing

set_option autoImplicit false

open scoped TensorProduct

namespace B26P

section Patch

variable {𝒪 : Type} [CommRing 𝒪] (F : Type) [AddCommGroup F] [Module 𝒪 F]
variable {B B' B'' P : Type} [CommRing B] [CommRing B'] [CommRing B''] [CommRing P]
  [Algebra 𝒪 B] [Algebra 𝒪 B'] [Algebra 𝒪 B''] [Algebra 𝒪 P]

noncomputable abbrev T {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y] (f : X →ₐ[𝒪] Y) :
    X ⊗[𝒪] F →ₗ[𝒪] Y ⊗[𝒪] F :=
  LinearMap.rTensor F f.toLinearMap

theorem T_smul {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y] (f : X →ₐ[𝒪] Y) (c : X)
    (x : X ⊗[𝒪] F) : T F f (c • x) = f c • T F f x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul b v =>
    rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.smul_tmul',
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul, smul_eq_mul, map_mul]

theorem T_comp {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z] [Algebra 𝒪 X] [Algebra 𝒪 Y] [Algebra 𝒪 Z]
    (f : X →ₐ[𝒪] Y) (g : Y →ₐ[𝒪] Z) (x : X ⊗[𝒪] F) : T F g (T F f x) = T F (g.comp f) x := by
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]; rfl

theorem T_one_tmul {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y] (f : X →ₐ[𝒪] Y) (v : F) :
    T F f ((1 : X) ⊗ₜ[𝒪] v) = (1 : Y) ⊗ₜ[𝒪] v := by
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

variable (φ' : B' →ₐ[𝒪] B) (φ'' : B'' →ₐ[𝒪] B) (p' : P →ₐ[𝒪] B') (p'' : P →ₐ[𝒪] B'')

def ιP : P →ₗ[𝒪] B' × B'' := p'.toLinearMap.prod p''.toLinearMap

def δB : B' × B'' →ₗ[𝒪] B :=
  φ'.toLinearMap.comp (LinearMap.fst 𝒪 B' B'') - φ''.toLinearMap.comp (LinearMap.snd 𝒪 B' B'')

theorem fst_comp_ιP : (LinearMap.fst 𝒪 B' B'').comp (ιP p' p'') = p'.toLinearMap := LinearMap.fst_prod _ _
theorem snd_comp_ιP : (LinearMap.snd 𝒪 B' B'').comp (ιP p' p'') = p''.toLinearMap := LinearMap.snd_prod _ _
theorem δB_comp_inl : (δB φ' φ'').comp (LinearMap.inl 𝒪 B' B'') = φ'.toLinearMap := by
  apply LinearMap.ext; intro x; simp [δB]
theorem δB_comp_inr : (δB φ' φ'').comp (LinearMap.inr 𝒪 B' B'') = -φ''.toLinearMap := by
  apply LinearMap.ext; intro x; simp [δB]

variable (hsq : ∀ x, φ' (p' x) = φ'' (p'' x))
  (hinj : ∀ x, p' x = 0 → p'' x = 0 → x = 0)
  (hpatch : ∀ b' b'', φ' b' = φ'' b'' → ∃ x, p' x = b' ∧ p'' x = b'')

include hinj in
theorem ιP_injective : Function.Injective (ιP p' p'') := by
  intro x y h
  have h1 : p' x = p' y := congrArg Prod.fst h
  have h2 : p'' x = p'' y := congrArg Prod.snd h
  have := hinj (x - y) (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self])
  exact sub_eq_zero.1 this

include hsq hpatch in
theorem exact_ιP_δB : Function.Exact (ιP p' p'') (δB φ' φ'') := by
  intro y
  constructor
  · intro hy
    have h : φ' y.1 = φ'' y.2 := by
      have : φ' y.1 - φ'' y.2 = 0 := hy
      exact sub_eq_zero.1 this
    obtain ⟨x, hx1, hx2⟩ := hpatch y.1 y.2 h
    exact ⟨x, Prod.ext hx1 hx2⟩
  · rintro ⟨x, rfl⟩
    show φ' (p' x) - φ'' (p'' x) = 0
    rw [hsq, sub_self]

variable [Module.Flat 𝒪 F]

include hinj in

theorem tensor_inj (x : P ⊗[𝒪] F) (h1 : T F p' x = 0) (h2 : T F p'' x = 0) : x = 0 := by
  have hι := Module.Flat.rTensor_preserves_injective_linearMap (M := F) (ιP p' p'') (ιP_injective p' p'' hinj)
  apply hι
  rw [map_zero]
  have hsum : (LinearMap.inl 𝒪 B' B'').comp (LinearMap.fst 𝒪 B' B'') +
      (LinearMap.inr 𝒪 B' B'').comp (LinearMap.snd 𝒪 B' B'') = LinearMap.id := by
    apply LinearMap.ext; intro y; simp
  have hid : ((LinearMap.inl 𝒪 B' B'').rTensor F).comp ((LinearMap.fst 𝒪 B' B'').rTensor F) +
      ((LinearMap.inr 𝒪 B' B'').rTensor F).comp ((LinearMap.snd 𝒪 B' B'').rTensor F) =
      (LinearMap.id : (B' × B'') ⊗[𝒪] F →ₗ[𝒪] (B' × B'') ⊗[𝒪] F) := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_add, hsum, LinearMap.rTensor_id]
  have e := LinearMap.congr_fun hid ((ιP p' p'').rTensor F x)
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply] at e
  have f1 : (LinearMap.fst 𝒪 B' B'').rTensor F ((ιP p' p'').rTensor F x) = T F p' x := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, fst_comp_ιP]
  have f2 : (LinearMap.snd 𝒪 B' B'').rTensor F ((ιP p' p'').rTensor F x) = T F p'' x := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, snd_comp_ιP]
  rw [← e, f1, f2, h1, h2, map_zero, map_zero, add_zero]

include hsq hpatch in

theorem tensor_patch (y' : B' ⊗[𝒪] F) (y'' : B'' ⊗[𝒪] F) (h : T F φ' y' = T F φ'' y'') :
    ∃ x : P ⊗[𝒪] F, T F p' x = y' ∧ T F p'' x = y'' := by
  have hex := Module.Flat.rTensor_exact F (exact_ιP_δB φ' φ'' p' p'' hsq hpatch)
  set z := (LinearMap.inl 𝒪 B' B'').rTensor F y' + (LinearMap.inr 𝒪 B' B'').rTensor F y'' with hz
  have hδ : (δB φ' φ'').rTensor F z = 0 := by
    rw [hz, map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← LinearMap.rTensor_comp, δB_comp_inl, δB_comp_inr, LinearMap.rTensor_neg, LinearMap.neg_apply]
    show T F φ' y' + -T F φ'' y'' = 0
    rw [h, add_neg_cancel]
  obtain ⟨x, hx⟩ := (hex z).1 hδ
  refine ⟨x, ?_, ?_⟩
  · have e : T F p' x = (LinearMap.fst 𝒪 B' B'').rTensor F ((ιP p' p'').rTensor F x) := by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, fst_comp_ιP]
    rw [e, hx, hz, map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← LinearMap.rTensor_comp, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, LinearMap.rTensor_id,
      LinearMap.rTensor_zero, LinearMap.id_apply, LinearMap.zero_apply, add_zero]
  · have e : T F p'' x = (LinearMap.snd 𝒪 B' B'').rTensor F ((ιP p' p'').rTensor F x) := by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, snd_comp_ιP]
    rw [e, hx, hz, map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← LinearMap.rTensor_comp, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, LinearMap.rTensor_id,
      LinearMap.rTensor_zero, LinearMap.id_apply, LinearMap.zero_apply, zero_add]

omit hsq hinj hpatch in

def spanImage {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y] (f : X →ₐ[𝒪] Y)
    (N : Submodule X (X ⊗[𝒪] F)) : Submodule Y (Y ⊗[𝒪] F) :=
  Submodule.span Y ((T F f) '' (N : Set (X ⊗[𝒪] F)))

omit hsq hinj hpatch in
theorem mem_spanImage_iff_of_surjective {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y]
    (f : X →ₐ[𝒪] Y) (hf : Function.Surjective f) (N : Submodule X (X ⊗[𝒪] F)) (y : Y ⊗[𝒪] F) :
    y ∈ spanImage F f N ↔ ∃ n ∈ N, T F f n = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨n, hn, rfl⟩ := hx; exact ⟨n, hn, rfl⟩
    | zero => exact ⟨0, N.zero_mem, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, hn, rfl⟩ := hx; obtain ⟨m, hm, rfl⟩ := hy
      exact ⟨n + m, N.add_mem hn hm, map_add _ _ _⟩
    | smul c x _ hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hf c
      exact ⟨c' • n, N.smul_mem c' hn, T_smul F f c' n⟩
  · rintro ⟨n, hn, rfl⟩
    exact Submodule.subset_span ⟨n, hn, rfl⟩

omit hsq hinj hpatch in
theorem spanImage_le_iff {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y]
    (f : X →ₐ[𝒪] Y) (N : Submodule X (X ⊗[𝒪] F)) (N' : Submodule Y (Y ⊗[𝒪] F)) :
    spanImage F f N ≤ N' ↔ ∀ n ∈ N, T F f n ∈ N' := by
  rw [spanImage, Submodule.span_le, Set.image_subset_iff]
  rfl

private def _root_.B26P.patch (N' : Submodule B' (B' ⊗[𝒪] F)) (N'' : Submodule B'' (B'' ⊗[𝒪] F)) : Submodule P (P ⊗[𝒪] F) where
  carrier := {x | T F p' x ∈ N' ∧ T F p'' x ∈ N''}
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact ⟨N'.zero_mem, N''.zero_mem⟩
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add]
    exact ⟨N'.add_mem ha.1 hb.1, N''.add_mem ha.2 hb.2⟩
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, T_smul]
    exact ⟨N'.smul_mem _ hx.1, N''.smul_mem _ hx.2⟩

p2m_export "B26P" "patch"
omit hsq hinj hpatch in
theorem mem_patch (N' : Submodule B' (B' ⊗[𝒪] F)) (N'' : Submodule B'' (B'' ⊗[𝒪] F)) (x : P ⊗[𝒪] F) :
    x ∈ patch F p' p'' N' N'' ↔ T F p' x ∈ N' ∧ T F p'' x ∈ N'' := Iff.rfl

variable (N' : Submodule B' (B' ⊗[𝒪] F)) (N'' : Submodule B'' (B'' ⊗[𝒪] F))
  (hN : spanImage F φ' N' = spanImage F φ'' N'')
  (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')

include hsq hpatch hN hs'' in

theorem spanImage_fst_patch : spanImage F p' (patch F p' p'' N' N'') = N' := by
  apply le_antisymm
  · rw [spanImage_le_iff]; intro n hn; exact hn.1
  · intro n' hn'
    have h1 : T F φ' n' ∈ spanImage F φ'' N'' := hN ▸ Submodule.subset_span ⟨n', hn', rfl⟩
    obtain ⟨n'', hn'', he⟩ := (mem_spanImage_iff_of_surjective F φ'' hs'' N'' _).1 h1
    obtain ⟨x, hx1, hx2⟩ := tensor_patch F φ' φ'' p' p'' hsq hpatch n' n'' he.symm
    exact Submodule.subset_span ⟨x, ⟨hx1 ▸ hn', hx2 ▸ hn''⟩, hx1⟩

include hsq hpatch hN hs' in

theorem spanImage_snd_patch : spanImage F p'' (patch F p' p'' N' N'') = N'' := by
  apply le_antisymm
  · rw [spanImage_le_iff]; intro n hn; exact hn.2
  · intro n'' hn''
    have h1 : T F φ'' n'' ∈ spanImage F φ' N' := hN.symm ▸ Submodule.subset_span ⟨n'', hn'', rfl⟩
    obtain ⟨n', hn', he⟩ := (mem_spanImage_iff_of_surjective F φ' hs' N' _).1 h1
    obtain ⟨x, hx1, hx2⟩ := tensor_patch F φ' φ'' p' p'' hsq hpatch n' n'' he
    exact Submodule.subset_span ⟨x, ⟨hx1 ▸ hn', hx2 ▸ hn''⟩, hx2⟩

omit hsq hinj hpatch hN hs' hs'' in

theorem eq_patch_of_spanImage_eq (Ñ : Submodule P (P ⊗[𝒪] F))
    (h1 : spanImage F p' Ñ = N') (h2 : spanImage F p'' Ñ = N'')
    (hÑ : Module.Invertible P ((P ⊗[𝒪] F) ⧸ Ñ)) (hNP : Module.Invertible P ((P ⊗[𝒪] F) ⧸ patch F p' p'' N' N'')) :
    Ñ = patch F p' p'' N' N'' := by
  have hle : Ñ ≤ patch F p' p'' N' N'' := by
    intro x hx
    exact ⟨h1 ▸ Submodule.subset_span ⟨x, hx, rfl⟩, h2 ▸ Submodule.subset_span ⟨x, hx, rfl⟩⟩
  apply le_antisymm hle
  intro x hx
  haveI := hÑ; haveI := hNP
  have hbij := Module.Invertible.bijective_of_surjective (Submodule.factor_surjective hle)
  have h0 : Submodule.factor hle (Submodule.Quotient.mk x) = Submodule.factor hle 0 := by
    rw [map_zero]
    show Submodule.factor hle (Submodule.mkQ Ñ x) = 0
    rw [Submodule.factor_mk]
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have := hbij.1 h0
  exact (Submodule.Quotient.mk_eq_zero Ñ).1 this

end Patch

end B26P

set_option autoImplicit false

open scoped TensorProduct

namespace B26P

section KerTensor

variable {𝒪 : Type} [CommRing 𝒪] (F : Type) [AddCommGroup F] [Module 𝒪 F]
variable {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y] (f : X →ₐ[𝒪] Y)

theorem ker_rTensor_eq_ker_smul_top (hf : Function.Surjective f) :
    (LinearMap.ker (LinearMap.rTensor F f.toLinearMap)).restrictScalars 𝒪 =
      ((RingHom.ker f.toRingHom • (⊤ : Submodule X (X ⊗[𝒪] F))).restrictScalars 𝒪) := by

  have hex : Function.Exact ((RingHom.ker f.toRingHom).restrictScalars 𝒪).subtype f.toLinearMap := by
    intro x
    simp only [LinearMap.mem_range, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact y.2
  have hT := rTensor_exact F hex hf
  ext z
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker]
  rw [show (LinearMap.rTensor F f.toLinearMap z = 0) ↔ z ∈ LinearMap.range (LinearMap.rTensor F
      ((RingHom.ker f.toRingHom).restrictScalars 𝒪).subtype) from ⟨fun h => (hT z).1 h, fun h => (hT z).2 h⟩]
  constructor
  · rintro ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul j v =>
      rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
      have : ((j : X) ⊗ₜ[𝒪] v : X ⊗[𝒪] F) = (j : X) • ((1 : X) ⊗ₜ[𝒪] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem_smul j.2 Submodule.mem_top
  · intro hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro j hj x _
      clear ‹x ∈ _›
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a b ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
      | tmul b v =>
        rw [TensorProduct.smul_tmul', smul_eq_mul]
        exact ⟨(⟨j * b, Ideal.mul_mem_right b _ hj⟩ : (RingHom.ker f.toRingHom).restrictScalars 𝒪) ⊗ₜ[𝒪] v,
          by rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]⟩
    · intro a b ha hb; exact Submodule.add_mem _ ha hb

theorem mem_ker_rTensor_iff (hf : Function.Surjective f) (z : X ⊗[𝒪] F) :
    LinearMap.rTensor F f.toLinearMap z = 0 ↔ z ∈ RingHom.ker f.toRingHom • (⊤ : Submodule X (X ⊗[𝒪] F)) := by
  have h := congrArg (fun S : Submodule 𝒪 (X ⊗[𝒪] F) => z ∈ S) (ker_rTensor_eq_ker_smul_top F f hf)
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker] at h
  exact Iff.of_eq h

end KerTensor

section Unipotent

variable {R : Type} [CommRing R] {L : Type} [AddCommGroup L] [Module R L]

theorem range_pow_le (J : Ideal R) (n : L →ₗ[R] L) (hn : LinearMap.range n ≤ J • ⊤) (m : ℕ) :
    LinearMap.range (n ^ m) ≤ J ^ m • ⊤ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rintro _ ⟨x, rfl⟩
    rw [pow_succ n m, Module.End.mul_apply]
    have hx : n x ∈ J • (⊤ : Submodule R L) := hn ⟨x, rfl⟩
    have h1 : (J • (⊤ : Submodule R L)).map (n ^ m) ≤ J ^ (m + 1) • ⊤ := by
      rw [Submodule.map_smul'', pow_succ' J m, Submodule.mul_smul]
      exact Submodule.smul_mono le_rfl (by rintro _ ⟨y, _, rfl⟩; exact ih ⟨y, rfl⟩)
    exact h1 ⟨n x, hx, rfl⟩

theorem isNilpotent_of_range_le (J : Ideal R) (hJ : IsNilpotent J) (n : L →ₗ[R] L)
    (hn : LinearMap.range n ≤ J • ⊤) : IsNilpotent n := by
  obtain ⟨k, hk⟩ := hJ
  refine ⟨k, ?_⟩
  apply LinearMap.ext; intro x
  have := range_pow_le J n hn k ⟨x, rfl⟩
  rw [hk, Ideal.zero_eq_bot, Submodule.bot_smul] at this
  simpa using this

theorem isUnit_of_range_sub_le (J : Ideal R) (hJ : IsNilpotent J) (u : L →ₗ[R] L)
    (hu : LinearMap.range (LinearMap.id - u) ≤ J • ⊤) : IsUnit u := by
  have h := (isNilpotent_of_range_le J hJ _ hu).isUnit_one_sub
  rwa [show (1 : L →ₗ[R] L) - (LinearMap.id - u) = u from sub_sub_cancel _ u] at h

end Unipotent

end B26P

set_option autoImplicit false

open scoped TensorProduct

namespace B26P

section Lift

variable {𝒪 : Type} [CommRing 𝒪] (F : Type) [AddCommGroup F] [Module 𝒪 F]
variable [Module.Flat 𝒪 F] {X B : Type} [CommRing X] [CommRing B] [Algebra 𝒪 X] [Algebra 𝒪 B] (f : X →ₐ[𝒪] B)

noncomputable def TfX : letI : Module X (B ⊗[𝒪] F) := Module.compHom (B ⊗[𝒪] F) f.toRingHom;
    X ⊗[𝒪] F →ₗ[X] B ⊗[𝒪] F :=
  letI : Module X (B ⊗[𝒪] F) := Module.compHom (B ⊗[𝒪] F) f.toRingHom
  { toFun := T F f
    map_add' := fun a b => map_add _ a b
    map_smul' := fun c y => by
      show T F f (c • y) = f c • T F f y
      exact T_smul F f c y }

def resX (e : B ⊗[𝒪] F →ₗ[B] B ⊗[𝒪] F) : letI : Module X (B ⊗[𝒪] F) := Module.compHom (B ⊗[𝒪] F) f.toRingHom;
    B ⊗[𝒪] F →ₗ[X] B ⊗[𝒪] F :=
  letI : Module X (B ⊗[𝒪] F) := Module.compHom (B ⊗[𝒪] F) f.toRingHom
  { toFun := e
    map_add' := fun a b => map_add _ a b
    map_smul' := fun c y => by
      show e (f c • y) = f c • e y
      exact e.map_smul _ _ }

theorem exists_idempotent_lift (hf : Function.Surjective f) (hJ : IsNilpotent (RingHom.ker f.toRingHom))
    (NX : Submodule X (X ⊗[𝒪] F)) [Module.Projective X ((X ⊗[𝒪] F) ⧸ NX)]
    (eB : B ⊗[𝒪] F →ₗ[B] B ⊗[𝒪] F) (heB : ∀ z, eB (eB z) = eB z)
    (hker : ∀ z, eB z = 0 ↔ z ∈ spanImage F f NX) :
    ∃ eX : X ⊗[𝒪] F →ₗ[X] X ⊗[𝒪] F, (∀ y, eX (eX y) = eX y) ∧ (∀ y, eX y = 0 ↔ y ∈ NX) ∧
      ∀ y, T F f (eX y) = eB (T F f y) := by
  letI instM : Module X (B ⊗[𝒪] F) := Module.compHom (B ⊗[𝒪] F) f.toRingHom
  set J : Ideal X := RingHom.ker f.toRingHom with hJdef

  let g : X ⊗[𝒪] F →ₗ[X] B ⊗[𝒪] F := (resX F f eB).comp (TfX F f)
  have hg : ∀ y, g y = eB (T F f y) := fun y => rfl
  have hNg : NX ≤ LinearMap.ker g := by
    intro n hn
    rw [LinearMap.mem_ker, hg, hker]
    exact Submodule.subset_span ⟨n, hn, rfl⟩
  let gbar : (X ⊗[𝒪] F ⧸ NX) →ₗ[X] B ⊗[𝒪] F := NX.liftQ g hNg
  have hgbar : ∀ y, gbar (NX.mkQ y) = eB (T F f y) := fun y => by
    show NX.liftQ g hNg (Submodule.Quotient.mk y) = _
    rw [Submodule.liftQ_apply]; rfl

  have hsurjT : Function.Surjective (TfX F f) := by
    intro z
    obtain ⟨y, hy⟩ := LinearMap.rTensor_surjective F (g := f.toLinearMap) hf z
    exact ⟨y, hy⟩
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (TfX F f) gbar hsurjT
  have ht' : ∀ l, T F f (t l) = gbar l := fun l => LinearMap.congr_fun ht l

  let u : (X ⊗[𝒪] F ⧸ NX) →ₗ[X] (X ⊗[𝒪] F ⧸ NX) := NX.mkQ.comp t
  have hu : ∀ l, u l = NX.mkQ (t l) := fun l => rfl
  have hrange : LinearMap.range (LinearMap.id - u) ≤ J • ⊤ := by
    rintro _ ⟨l, rfl⟩
    obtain ⟨y, rfl⟩ := NX.mkQ_surjective l

    have hw : T F f y - eB (T F f y) ∈ spanImage F f NX := by
      rw [← hker, map_sub, heB, sub_self]
    obtain ⟨n, hn, hTn⟩ := (mem_spanImage_iff_of_surjective F f hf NX _).1 hw
    have hz : T F f (y - n - t (NX.mkQ y)) = 0 := by
      rw [map_sub, map_sub, hTn, ht', hgbar]; abel
    have hz' : y - n - t (NX.mkQ y) ∈ J • (⊤ : Submodule X (X ⊗[𝒪] F)) :=
      (mem_ker_rTensor_iff F f hf _).1 hz
    have hq : NX.mkQ (y - n - t (NX.mkQ y)) ∈ (J • (⊤ : Submodule X (X ⊗[𝒪] F))).map NX.mkQ :=
      Submodule.mem_map_of_mem hz'
    have hn0 : NX.mkQ n = 0 := by rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero NX).2 hn
    rw [Submodule.map_smul'', map_sub, map_sub, hn0, sub_zero] at hq
    show NX.mkQ y - NX.mkQ (t (NX.mkQ y)) ∈ J • ⊤
    exact Submodule.smul_mono le_rfl le_top hq

  obtain ⟨w, hw⟩ := isUnit_of_range_sub_le J hJ u hrange
  have huw : ∀ l, u ((↑w⁻¹ : (X ⊗[𝒪] F ⧸ NX) →ₗ[X] (X ⊗[𝒪] F ⧸ NX)) l) = l := by
    intro l
    have e1 := congrArg (fun φ : Module.End X (X ⊗[𝒪] F ⧸ NX) => φ l) (Units.mul_inv w)
    simp only [Module.End.mul_apply, Module.End.one_apply] at e1
    rwa [hw] at e1
  have hwinv : ∀ l, NX.mkQ (t ((↑w⁻¹ : (X ⊗[𝒪] F ⧸ NX) →ₗ[X] (X ⊗[𝒪] F ⧸ NX)) l)) = l := fun l => huw l

  have hgu : ∀ l, gbar (u l) = gbar l := by
    intro l
    obtain ⟨y, rfl⟩ := NX.mkQ_surjective l
    show gbar (NX.mkQ (t (NX.mkQ y))) = gbar (NX.mkQ y)
    rw [hgbar, ht', hgbar, heB]
  have hgw : ∀ l, gbar ((↑w⁻¹ : (X ⊗[𝒪] F ⧸ NX) →ₗ[X] _) l) = gbar l := by
    intro l
    have h1 := hgu ((↑w⁻¹ : (X ⊗[𝒪] F ⧸ NX) →ₗ[X] _) l)
    rw [huw] at h1
    exact h1.symm

  let eX : X ⊗[𝒪] F →ₗ[X] X ⊗[𝒪] F := t.comp ((↑w⁻¹ : (X ⊗[𝒪] F ⧸ NX) →ₗ[X] _).comp NX.mkQ)
  have heX : ∀ y, eX y = t ((↑w⁻¹ : (X ⊗[𝒪] F ⧸ NX) →ₗ[X] _) (NX.mkQ y)) := fun y => rfl
  have hqeX : ∀ y, NX.mkQ (eX y) = NX.mkQ y := fun y => by rw [heX, hwinv]
  refine ⟨eX, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [heX (eX y), hqeX, ← heX]
  · constructor
    · intro h
      have := hqeX y
      rw [h, map_zero] at this
      exact (Submodule.Quotient.mk_eq_zero NX).1 this.symm
    · intro hy
      have hy0 : NX.mkQ y = 0 := by rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero NX).2 hy
      rw [heX, hy0, map_zero, map_zero]
  · rw [heX, ht', hgw, hgbar]

end Lift

end B26P

set_option autoImplicit false

open scoped TensorProduct

namespace B26P

section InvQuot

variable {𝒪 : Type} [CommRing 𝒪] (F : Type) [AddCommGroup F] [Module 𝒪 F] [Module.Flat 𝒪 F]
variable {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y] (f : X →ₐ[𝒪] Y)

theorem spanImage_eq_ker [Algebra X Y] [IsScalarTower 𝒪 X Y] (hf : ∀ b, algebraMap X Y b = f b)
    (N : Submodule X (X ⊗[𝒪] F)) :
    spanImage F f N = LinearMap.ker (Module.Grassmannian.baseChangeMkQ Y N) := by
  have hker : LinearMap.ker (N.mkQ.baseChange Y) = N.baseChange Y := by
    ext x
    have hx : x ∈ LinearMap.ker (LinearMap.lTensor Y N.mkQ) ↔ x ∈ LinearMap.range (LinearMap.lTensor Y N.subtype) := by
      rw [lTensor_mkQ (Q := Y)]
    rw [LinearMap.mem_ker, LinearMap.mem_range] at hx
    rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor, hx, Submodule.baseChange, LinearMap.mem_range,
      LinearMap.baseChange_eq_ltensor]
  have hc : ∀ x : X ⊗[𝒪] F, TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 X Y Y F ((1 : Y) ⊗ₜ[X] x) = T F f x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
    | tmul b v =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        Algebra.smul_def, hf, mul_one]
    | add x y hx hy => rw [TensorProduct.tmul_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]
  rw [Module.Grassmannian.baseChangeMkQ, LinearMap.ker_comp, hker, ← Submodule.map_equiv_eq_comap_symm,
    Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image, spanImage]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact (hc x).symm

theorem invertible_quotient_spanImage (N : Submodule X (X ⊗[𝒪] F))
    (hN : Module.Invertible X ((X ⊗[𝒪] F) ⧸ N)) :
    Module.Invertible Y ((Y ⊗[𝒪] F) ⧸ spanImage F f N) := by
  letI : Algebra X Y := f.toAlgebra
  haveI : IsScalarTower 𝒪 X Y := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  haveI := hN
  exact Module.Invertible.congr
    ((Module.Grassmannian.baseChangeMkQEquiv (B := Y) N).symm.trans
      (Submodule.quotEquivOfEq _ _ (spanImage_eq_ker F f (fun _ => rfl) N).symm))

theorem exists_idempotent_of_projective_quotient (N : Submodule X (X ⊗[𝒪] F))
    [Module.Projective X ((X ⊗[𝒪] F) ⧸ N)] :
    ∃ e : X ⊗[𝒪] F →ₗ[X] X ⊗[𝒪] F, (∀ y, e (e y) = e y) ∧ ∀ y, e y = 0 ↔ y ∈ N := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id) N.mkQ_surjective
  have hs' : ∀ l, N.mkQ (s l) = l := fun l => LinearMap.congr_fun hs l
  refine ⟨s.comp N.mkQ, fun y => ?_, fun y => ?_⟩
  · show s (N.mkQ (s (N.mkQ y))) = s (N.mkQ y); rw [hs']
  · show s (N.mkQ y) = 0 ↔ y ∈ N
    constructor
    · intro h
      have := hs' (N.mkQ y); rw [h, map_zero] at this
      rw [Submodule.mkQ_apply] at this
      exact (Submodule.Quotient.mk_eq_zero N).1 this.symm
    · intro hy
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]

end InvQuot

end B26P

set_option autoImplicit false

open scoped TensorProduct

namespace B26P

section PatchIdem

variable {𝒪 : Type} [CommRing 𝒪] (F : Type) [AddCommGroup F] [Module 𝒪 F] [Module.Flat 𝒪 F]
variable {B B' B'' P : Type} [CommRing B] [CommRing B'] [CommRing B''] [CommRing P]
  [Algebra 𝒪 B] [Algebra 𝒪 B'] [Algebra 𝒪 B''] [Algebra 𝒪 P]
variable (φ' : B' →ₐ[𝒪] B) (φ'' : B'' →ₐ[𝒪] B) (p' : P →ₐ[𝒪] B') (p'' : P →ₐ[𝒪] B'')
variable (hsq : ∀ x, φ' (p' x) = φ'' (p'' x))
  (hinj : ∀ x, p' x = 0 → p'' x = 0 → x = 0)
  (hpatch : ∀ b' b'', φ' b' = φ'' b'' → ∃ x, p' x = b' ∧ p'' x = b'')
variable (N' : Submodule B' (B' ⊗[𝒪] F)) (N'' : Submodule B'' (B'' ⊗[𝒪] F))
  (hN : spanImage F φ' N' = spanImage F φ'' N'')
  (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
  (hJ' : IsNilpotent (RingHom.ker φ'.toRingHom)) (hJ'' : IsNilpotent (RingHom.ker φ''.toRingHom))

include hsq in
theorem T_comp_eq (x : P ⊗[𝒪] F) : T F φ' (T F p' x) = T F φ'' (T F p'' x) := by
  rw [T_comp, T_comp]
  have : φ'.comp p' = φ''.comp p'' := AlgHom.ext hsq
  rw [this]

include hsq hinj hpatch hN hs' hs'' hJ' hJ'' in

theorem exists_idempotent_patch [Module.Invertible B' ((B' ⊗[𝒪] F) ⧸ N')]
    [Module.Invertible B'' ((B'' ⊗[𝒪] F) ⧸ N'')] :
    ∃ e : P ⊗[𝒪] F →ₗ[P] P ⊗[𝒪] F, (∀ x, e (e x) = e x) ∧ ∀ x, e x = 0 ↔ x ∈ patch F p' p'' N' N'' := by

  haveI hNB : Module.Invertible B ((B ⊗[𝒪] F) ⧸ spanImage F φ' N') := invertible_quotient_spanImage F φ' N' inferInstance
  obtain ⟨eB, heB, hkerB⟩ := exists_idempotent_of_projective_quotient F (spanImage F φ' N')

  obtain ⟨e', he', hker', hc'⟩ := exists_idempotent_lift F φ' hs' hJ' N' eB heB hkerB
  obtain ⟨e'', he'', hker'', hc''⟩ := exists_idempotent_lift F φ'' hs'' hJ'' N'' eB heB (fun z => by rw [hkerB z, hN])

  have hcompat : ∀ x : P ⊗[𝒪] F, T F φ' (e' (T F p' x)) = T F φ'' (e'' (T F p'' x)) := by
    intro x; rw [hc', hc'', T_comp_eq F φ' φ'' p' p'' hsq]
  choose ef hef1 hef2 using fun x : P ⊗[𝒪] F =>
    tensor_patch F φ' φ'' p' p'' hsq hpatch (e' (T F p' x)) (e'' (T F p'' x)) (hcompat x)
  have huniq : ∀ x y : P ⊗[𝒪] F, T F p' x = T F p' y → T F p'' x = T F p'' y → x = y := by
    intro x y h1 h2
    have := tensor_inj F p' p'' hinj (x - y) (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self])
    exact sub_eq_zero.1 this
  let e : P ⊗[𝒪] F →ₗ[P] P ⊗[𝒪] F :=
    { toFun := ef
      map_add' := fun a b => huniq _ _
        (by rw [hef1, map_add, map_add, map_add, hef1, hef1])
        (by rw [hef2, map_add, map_add, map_add, hef2, hef2])
      map_smul' := fun c a => huniq _ _
        (by rw [hef1, T_smul, map_smul, RingHom.id_apply, T_smul, hef1])
        (by rw [hef2, T_smul, map_smul, RingHom.id_apply, T_smul, hef2]) }
  have he : ∀ x, e x = ef x := fun x => rfl
  refine ⟨e, fun x => ?_, fun x => ?_⟩
  · apply huniq
    · rw [he, he, hef1, hef1, he']
    · rw [he, he, hef2, hef2, he'']
  · rw [mem_patch, ← hker', ← hker'']
    constructor
    · intro h
      have h1 := hef1 x; have h2 := hef2 x
      rw [← he, h, map_zero] at h1 h2
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      apply huniq
      · rw [he, hef1, h1, map_zero]
      · rw [he, hef2, h2, map_zero]

omit hsq hinj hpatch hN hs' hs'' hJ' hJ'' in

theorem projective_quotient_of_idempotent {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] (e : M →ₗ[R] M) (he : ∀ x, e (e x) = e x) (N : Submodule R M)
    (hN : ∀ x, e x = 0 ↔ x ∈ N) : Module.Projective R (M ⧸ N) := by
  have hker : LinearMap.ker e = N := by ext x; rw [LinearMap.mem_ker]; exact hN x

  have hP : Module.Projective R (LinearMap.range e) := by
    refine Module.Projective.of_split (LinearMap.range e).subtype (LinearMap.rangeRestrict e) ?_
    apply LinearMap.ext; intro x
    obtain ⟨y, hy⟩ := x.2
    apply Subtype.ext
    show e x.1 = x.1
    rw [← hy, he]
  have eqv : (M ⧸ N) ≃ₗ[R] LinearMap.range e := (Submodule.quotEquivOfEq _ _ hker.symm).trans e.quotKerEquivRange
  exact Module.Projective.of_equiv eqv.symm

end PatchIdem

end B26P

set_option autoImplicit false

open scoped TensorProduct

namespace B26P

section RankOne

variable {𝒪 : Type} [CommRing 𝒪] (F : Type) [AddCommGroup F] [Module 𝒪 F] [Module.Free 𝒪 F] [Module.Finite 𝒪 F]
variable {B B' B'' P : Type} [CommRing B] [CommRing B'] [CommRing B''] [CommRing P]
  [Algebra 𝒪 B] [Algebra 𝒪 B'] [Algebra 𝒪 B''] [Algebra 𝒪 P]
variable (φ' : B' →ₐ[𝒪] B) (φ'' : B'' →ₐ[𝒪] B) (p' : P →ₐ[𝒪] B') (p'' : P →ₐ[𝒪] B'')
variable (hsq : ∀ x, φ' (p' x) = φ'' (p'' x))
  (hinj : ∀ x, p' x = 0 → p'' x = 0 → x = 0)
  (hpatch : ∀ b' b'', φ' b' = φ'' b'' → ∃ x, p' x = b' ∧ p'' x = b'')
variable (N' : Submodule B' (B' ⊗[𝒪] F)) (N'' : Submodule B'' (B'' ⊗[𝒪] F))
  (hN : spanImage F φ' N' = spanImage F φ'' N'')
  (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
  (hJ' : IsNilpotent (RingHom.ker φ'.toRingHom)) (hJ'' : IsNilpotent (RingHom.ker φ''.toRingHom))

include hpatch hs'' in
theorem surjective_fst : Function.Surjective p' := by
  intro b'
  obtain ⟨b'', hb''⟩ := hs'' (φ' b')
  obtain ⟨x, hx, _⟩ := hpatch b' b'' hb''.symm
  exact ⟨x, hx⟩

include hsq hinj hJ'' in

theorem isNilpotent_of_fst_eq_zero (x : P) (hx : p' x = 0) : IsNilpotent x := by
  obtain ⟨k, hk⟩ := hJ''
  have h2 : p'' x ∈ RingHom.ker φ''.toRingHom := by
    show φ'' (p'' x) = 0
    rw [← hsq, hx, map_zero]
  by_cases hk0 : k = 0
  · subst hk0
    rw [pow_zero, Ideal.one_eq_top] at hk
    have h1 : (p'' x) ∈ (⊤ : Ideal B'') := trivial
    rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
    have := hinj x hx h1
    subst this
    exact IsNilpotent.zero
  refine ⟨k, hinj _ ?_ ?_⟩
  · rw [map_pow, hx, zero_pow hk0]
  · have := Ideal.pow_mem_pow h2 k
    rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    rw [map_pow]; exact this

include hsq hinj hpatch hs'' hJ'' in

theorem exists_ringHom_comp_fst (K : Type) [Field K] [Algebra P K] :
    ∃ τ : B' →+* K, ∀ x, τ (p' x) = algebraMap P K x := by
  have hvan : ∀ x ∈ RingHom.ker p'.toRingHom, algebraMap P K x = 0 := by
    intro x hx
    exact ((isNilpotent_of_fst_eq_zero φ' φ'' p' p'' hsq hinj hJ'' x hx).map (algebraMap P K)).eq_zero
  have hsurj := surjective_fst φ' φ'' p' p'' hpatch hs''
  let q : P ⧸ RingHom.ker p'.toRingHom →+* K := Ideal.Quotient.lift _ (algebraMap P K) hvan
  let ε : P ⧸ RingHom.ker p'.toRingHom ≃+* B' := RingHom.quotientKerEquivOfSurjective hsurj
  refine ⟨q.comp ε.symm.toRingHom, fun x => ?_⟩
  have hε : ε.symm (p' x) = Ideal.Quotient.mk _ x := by
    apply ε.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  show q (ε.symm (p' x)) = _
  rw [hε]
  rfl

include hsq hinj hpatch hN hs' hs'' hJ' hJ'' in

theorem invertible_quotient_patch [Module.Invertible B' ((B' ⊗[𝒪] F) ⧸ N')]
    [Module.Invertible B'' ((B'' ⊗[𝒪] F) ⧸ N'')] :
    Module.Invertible P ((P ⊗[𝒪] F) ⧸ patch F p' p'' N' N'') := by
  obtain ⟨e, he, hker⟩ := exists_idempotent_patch F φ' φ'' p' p'' hsq hinj hpatch N' N'' hN hs' hs'' hJ' hJ''
  haveI : Module.Projective P ((P ⊗[𝒪] F) ⧸ patch F p' p'' N' N'') :=
    projective_quotient_of_idempotent e he _ hker
  apply Module.Invertible.of_projective_of_forall_finrank_eq_one
  intro K _ _

  obtain ⟨τ, hτ⟩ := exists_ringHom_comp_fst φ' φ'' p' p'' hsq hinj hpatch hs'' hJ'' K
  letI : Algebra P B' := p'.toRingHom.toAlgebra
  haveI : IsScalarTower 𝒪 P B' := IsScalarTower.of_algebraMap_eq fun r => (p'.commutes r).symm
  letI : Algebra B' K := τ.toAlgebra
  haveI : IsScalarTower P B' K := IsScalarTower.of_algebraMap_eq fun x => (hτ x).symm

  have hk : spanImage F p' (patch F p' p'' N' N'') = LinearMap.ker (Module.Grassmannian.baseChangeMkQ B' (patch F p' p'' N' N'')) :=
    spanImage_eq_ker F p' (fun _ => rfl) _
  rw [spanImage_fst_patch F φ' φ'' p' p'' hsq hpatch N' N'' hN hs''] at hk
  let e1 : ((B' ⊗[𝒪] F) ⧸ N') ≃ₗ[B'] B' ⊗[P] ((P ⊗[𝒪] F) ⧸ patch F p' p'' N' N'') :=
    (Submodule.quotEquivOfEq _ _ hk).trans (Module.Grassmannian.baseChangeMkQEquiv (B := B') (patch F p' p'' N' N''))

  let e2 : K ⊗[P] ((P ⊗[𝒪] F) ⧸ patch F p' p'' N' N'') ≃ₗ[K] K ⊗[B'] ((B' ⊗[𝒪] F) ⧸ N') :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P B' K K ((P ⊗[𝒪] F) ⧸ patch F p' p'' N' N'')).symm.trans
      (LinearEquiv.baseChange B' K _ _ e1.symm)
  rw [e2.finrank_eq]
  exact Module.Invertible.finrank_eq_one K (K ⊗[B'] ((B' ⊗[𝒪] F) ⧸ N'))

end RankOne

end B26P

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B26P

section Deligne

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (hfree : ∀ M : FullLattice 𝒪 K, Module.Free 𝒪 ↥M.1) (hfin : ∀ M : FullLattice 𝒪 K, Module.Finite 𝒪 ↥M.1)
variable {B B' B'' P : Type} [CommRing B] [CommRing B'] [CommRing B''] [CommRing P]
  [Algebra 𝒪 B] [Algebra 𝒪 B'] [Algebra 𝒪 B''] [Algebra 𝒪 P]
variable (φ' : B' →ₐ[𝒪] B) (φ'' : B'' →ₐ[𝒪] B) (p' : P →ₐ[𝒪] B') (p'' : P →ₐ[𝒪] B'')
variable (hsq : ∀ x, φ' (p' x) = φ'' (p'' x))
  (hinj : ∀ x, p' x = 0 → p'' x = 0 → x = 0)
  (hpatch : ∀ b' b'', φ' b' = φ'' b'' → ∃ x, p' x = b' ∧ p'' x = b'')
  (hs' : Function.Surjective φ') (hs'' : Function.Surjective φ'')
  (hJ' : IsNilpotent (RingHom.ker φ'.toRingHom)) (hJ'' : IsNilpotent (RingHom.ker φ''.toRingHom))
variable (d' : DeligneDatum (K := K) π B') (d'' : DeligneDatum (K := K) π B'')
  (hd : d'.map π φ' = d''.map π φ'')

theorem lineBaseChange_eq_spanImage {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y]
    (f : X →ₐ[𝒪] Y) (M : FullLattice 𝒪 K) (N : Submodule X (latticeBaseChange 𝒪 K X M)) :
    lineBaseChange f M N = spanImage (↥M.1) f N := rfl

include hd in
theorem line_compat (M : FullLattice 𝒪 K) :
    spanImage (↥M.1) φ' (d'.line M) = spanImage (↥M.1) φ'' (d''.line M) := by
  have := congrArg (fun d : DeligneDatum (K := K) π B => d.line M) hd
  exact this

theorem T_mem_sup {X Y : Type} [CommRing X] [CommRing Y] [Algebra 𝒪 X] [Algebra 𝒪 Y] (f : X →ₐ[𝒪] Y)
    (F : Type) [AddCommGroup F] [Module 𝒪 F]
    (N : Submodule X (X ⊗[𝒪] F)) (N₁ : Submodule Y (Y ⊗[𝒪] F)) (hN : ∀ n ∈ N, T F f n ∈ N₁) (𝔭 : Ideal X)
    (x : X ⊗[𝒪] F) (hx : x ∈ N ⊔ (𝔭 • ⊤ : Submodule X (X ⊗[𝒪] F))) :
    T F f x ∈ N₁ ⊔ ((𝔭.map f.toRingHom) • ⊤ : Submodule Y (Y ⊗[𝒪] F)) := by
  obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine Submodule.add_mem_sup (hN n hn) ?_
  refine Submodule.smul_induction_on (p := fun z => T F f z ∈ ((𝔭.map f.toRingHom) • ⊤ : Submodule Y (Y ⊗[𝒪] F))) hz
    ?_ ?_
  · intro r hr y _
    rw [T_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem f.toRingHom hr) Submodule.mem_top
  · intro a b ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb

namespace DeligneDatum
include hfree hfin hsq hinj hpatch hs' hs'' hJ' hJ'' hd in

private noncomputable def _root_.B26P.DeligneDatum.patch : DeligneDatum (K := K) π P where
  line M := B26P.patch (↥M.1) p' p'' (d'.line M) (d''.line M)
  invertible M := by
    haveI := hfree M; haveI := hfin M
    haveI := d'.invertible M; haveI := d''.invertible M
    exact invertible_quotient_patch (↥M.1) φ' φ'' p' p'' hsq hinj hpatch (d'.line M) (d''.line M)
      (line_compat π φ' φ'' d' d'' hd M) hs' hs'' hJ' hJ''
  mono {M' M} h := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := (mem_patch (↥M'.1) p' p'' _ _ x).1 hx
    rw [mem_patch]
    constructor
    · have := d'.mono h (Submodule.mem_map_of_mem hx'.1)
      rwa [← rTensor_inclBaseChange] at this
    · have := d''.mono h (Submodule.mem_map_of_mem hx'.2)
      rwa [← rTensor_inclBaseChange] at this
  homothety cK M := by
    ext x
    have e1 : ∀ {X : Type} [CommRing X] [Algebra 𝒪 X] (N : Submodule X (latticeBaseChange 𝒪 K X M))
        (y : latticeBaseChange 𝒪 K X (FullLattice.act (scalarGL cK) M)),
        y ∈ N.map (actBaseChange X (scalarGL cK) M).toLinearMap ↔ (actBaseChange X (scalarGL cK) M).symm y ∈ N := by
      intro X _ _ N y
      rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap]; rfl
    have e2 : ∀ {X : Type} [CommRing X] [Algebra 𝒪 X] (f : P →ₐ[𝒪] X) (y : latticeBaseChange 𝒪 K P (FullLattice.act (scalarGL cK) M)),
        (actBaseChange X (scalarGL cK) M).symm (LinearMap.rTensor _ f.toLinearMap y) =
          LinearMap.rTensor (↥M.1) f.toLinearMap ((actBaseChange P (scalarGL cK) M).symm y) := by
      intro X _ _ f y
      apply (actBaseChange X (scalarGL cK) M).injective
      rw [LinearEquiv.apply_symm_apply, ← rTensor_actBaseChange, LinearEquiv.apply_symm_apply]
    rw [mem_patch, d'.homothety cK M, d''.homothety cK M, e1, e1, e1, mem_patch]
    show (actBaseChange B' (scalarGL cK) M).symm (LinearMap.rTensor _ p'.toLinearMap x) ∈ d'.line M ∧
        (actBaseChange B'' (scalarGL cK) M).symm (LinearMap.rTensor _ p''.toLinearMap x) ∈ d''.line M ↔ _
    rw [e2, e2]
  nondeg 𝔭 h𝔭 := by
    have hs1 := surjective_fst φ' φ'' p' p'' hpatch hs''
    have hker : RingHom.ker p'.toRingHom ≤ 𝔭 := by
      intro x hx
      obtain ⟨k, hk⟩ := isNilpotent_of_fst_eq_zero φ' φ'' p' p'' hsq hinj hJ'' x hx
      exact h𝔭.mem_of_pow_mem k (hk ▸ 𝔭.zero_mem)
    haveI : 𝔭.IsPrime := h𝔭
    have h𝔮 : (𝔭.map p'.toRingHom).IsPrime := Ideal.map_isPrime_of_surjective hs1 hker
    obtain ⟨M', M, h, hπ, h1, h2⟩ := d'.nondeg (𝔭.map p'.toRingHom) h𝔮
    refine ⟨M', M, h, hπ, fun v hv hmem => ?_, fun v' hv' hmem => ?_⟩
    · apply h1 v hv
      have := T_mem_sup p' (↥M.1) (B26P.patch (↥M.1) p' p'' (d'.line M) (d''.line M)) (d'.line M)
        (fun n hn => ((mem_patch _ p' p'' _ _ n).1 hn).1) 𝔭 _ hmem
      rwa [T_one_tmul] at this
    · apply h2 v' hv'
      have := T_mem_sup p' (↥M'.1) (B26P.patch (↥M'.1) p' p'' (d'.line M') (d''.line M')) (d'.line M')
        (fun n hn => ((mem_patch _ p' p'' _ _ n).1 hn).1) 𝔭 _ hmem
      rwa [T_one_tmul] at this

end DeligneDatum
p2m_export "B26P" "DeligneDatum.patch"
include hfree hfin hsq hinj hpatch hs' hs'' hJ' hJ'' hd in
theorem DeligneDatum.patch_map_fst :
    (DeligneDatum.patch π hfree hfin φ' φ'' p' p'' hsq hinj hpatch hs' hs'' hJ' hJ'' d' d'' hd).map π p' = d' := by
  apply DeligneDatum.ext'
  funext M
  show lineBaseChange p' M (B26P.patch (↥M.1) p' p'' (d'.line M) (d''.line M)) = d'.line M
  rw [lineBaseChange_eq_spanImage]
  exact spanImage_fst_patch (↥M.1) φ' φ'' p' p'' hsq hpatch _ _ (line_compat π φ' φ'' d' d'' hd M) hs''

include hfree hfin hsq hinj hpatch hs' hs'' hJ' hJ'' hd in
theorem DeligneDatum.patch_map_snd :
    (DeligneDatum.patch π hfree hfin φ' φ'' p' p'' hsq hinj hpatch hs' hs'' hJ' hJ'' d' d'' hd).map π p'' = d'' := by
  apply DeligneDatum.ext'
  funext M
  show lineBaseChange p'' M (B26P.patch (↥M.1) p' p'' (d'.line M) (d''.line M)) = d''.line M
  rw [lineBaseChange_eq_spanImage]
  exact spanImage_snd_patch (↥M.1) φ' φ'' p' p'' hsq hpatch _ _ (line_compat π φ' φ'' d' d'' hd M) hs'

include hfree hfin hsq hinj hpatch hs' hs'' hJ' hJ'' hd in
theorem DeligneDatum.eq_patch (z : DeligneDatum (K := K) π P) (h1 : z.map π p' = d') (h2 : z.map π p'' = d'') :
    z = DeligneDatum.patch π hfree hfin φ' φ'' p' p'' hsq hinj hpatch hs' hs'' hJ' hJ'' d' d'' hd := by
  apply DeligneDatum.ext'
  funext M
  have e1 : spanImage (↥M.1) p' (z.line M) = d'.line M := congrArg (fun d : DeligneDatum (K := K) π B' => d.line M) h1
  have e2 : spanImage (↥M.1) p'' (z.line M) = d''.line M := congrArg (fun d : DeligneDatum (K := K) π B'' => d.line M) h2
  exact eq_patch_of_spanImage_eq (↥M.1) p' p'' (d'.line M) (d''.line M) (z.line M) e1 e2 (z.invertible M)
    ((DeligneDatum.patch π hfree hfin φ' φ'' p' p'' hsq hinj hpatch hs' hs'' hJ' hJ'' d' d'' hd).invertible M)

end Deligne

end B26P

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic TensorProduct
open LT.LatticeTree

namespace B26P

theorem free_of_fullLattice (p : ℕ) [Fact p.Prime] (M : FullLattice ℤ_[p] ℚ_[p]) : Module.Free ℤ_[p] ↥M.1 := by
  haveI : Module.Finite ℤ_[p] ↥M.1 := Module.Finite.iff_fg.mpr M.2.1
  exact Module.free_of_finite_type_torsion_free'

theorem finite_of_fullLattice (p : ℕ) [Fact p.Prime] (M : FullLattice ℤ_[p] ℚ_[p]) : Module.Finite ℤ_[p] ↥M.1 :=
  Module.Finite.iff_fg.mpr M.2.1

end B26P

theorem solution
    (p : ℕ) [Fact p.Prime] (π : ℤ_[p]) {O : Type} [CommRing O] (c : ℤ_[p] →+* O)
    :
    (∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B] [IsNoetherianRing B'] [IsNoetherianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_hs' : Function.Surjective φ') (_hs'' : Function.Surjective φ'')
    (_hn' : IsNilpotent (RingHom.ker φ')) (_hn'' : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : ModuliPackage.pullbackRing φ' φ''))
    (x' : (omegaPackage (K := ℚ_[p]) p π c).obj B' ψ' hB') (x'' : (omegaPackage (K := ℚ_[p]) p π c).obj B'' ψ'' hB''),
      (omegaPackage (K := ℚ_[p]) p π c).map hB' hB φ' hφ' x' = (omegaPackage (K := ℚ_[p]) p π c).map hB'' hB φ'' hφ'' x'' →
      ∃! z : (omegaPackage (K := ℚ_[p]) p π c).obj (ModuliPackage.pullbackRing φ' φ'')
          (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        (omegaPackage (K := ℚ_[p]) p π c).map hP hB' (ModuliPackage.pullbackFst φ' φ'')
            (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        (omegaPackage (K := ℚ_[p]) p π c).map hP hB'' (ModuliPackage.pullbackSnd φ' φ'')
            (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'') := by
  intro B B' B'' _ _ _ _ _ _ ψ ψ' ψ'' hB hB' hB'' φ' φ'' hφ' hφ'' hs' hs'' hn' hn'' hP x' x'' hx
  letI aB : Algebra ℤ_[p] B := (ψ.comp c).toAlgebra
  letI aB' : Algebra ℤ_[p] B' := (ψ'.comp c).toAlgebra
  letI aB'' : Algebra ℤ_[p] B'' := (ψ''.comp c).toAlgebra
  letI aP : Algebra ℤ_[p] (ModuliPackage.pullbackRing φ' φ'') :=
    ((ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)).comp c).toAlgebra
  let Φ' := AlgFunctor.algHomOfComp c ψ' ψ φ' hφ'
  let Φ'' := AlgFunctor.algHomOfComp c ψ'' ψ φ'' hφ''
  let P' := AlgFunctor.algHomOfComp c (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) ψ'
    (ModuliPackage.pullbackFst φ' φ'') (ModuliPackage.pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _)
  let P'' := AlgFunctor.algHomOfComp c (ModuliPackage.pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) ψ''
    (ModuliPackage.pullbackSnd φ' φ'') (ModuliPackage.pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _)
  have hsq : ∀ x, Φ' (P' x) = Φ'' (P'' x) := fun x => x.2
  have hinj : ∀ x, P' x = 0 → P'' x = 0 → x = 0 := fun x h1 h2 => Subtype.ext (Prod.ext h1 h2)
  have hpatch : ∀ b' b'', Φ' b' = Φ'' b'' → ∃ x, P' x = b' ∧ P'' x = b'' :=
    fun b' b'' h => ⟨⟨(b', b''), h⟩, rfl, rfl⟩
  have hfree := B26P.free_of_fullLattice p
  have hfin := B26P.finite_of_fullLattice p
  have hd : DeligneDatum.map π Φ' x' = DeligneDatum.map π Φ'' x'' := hx
  refine ⟨B26P.DeligneDatum.patch π hfree hfin Φ' Φ'' P' P'' hsq hinj hpatch hs' hs'' hn' hn'' x' x'' hd, ⟨?_, ?_⟩, ?_⟩
  · exact B26P.DeligneDatum.patch_map_fst π hfree hfin Φ' Φ'' P' P'' hsq hinj hpatch hs' hs'' hn' hn'' x' x'' hd
  · exact B26P.DeligneDatum.patch_map_snd π hfree hfin Φ' Φ'' P' P'' hsq hinj hpatch hs' hs'' hn' hn'' x' x'' hd
  · rintro z ⟨h1, h2⟩
    exact B26P.DeligneDatum.eq_patch π hfree hfin Φ' Φ'' P' P'' hsq hinj hpatch hs' hs'' hn' hn'' x' x'' hd z h1 h2

end S_CerednikDrinfeld_FormalOmega_omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_omegaPackage_padic_existsUnique_map_pullbackFst_eq_and_map_pullbackSnd_eq_of_isNoetherianRing (solution)
