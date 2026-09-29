-- Prove2me | solution 1 for DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/82b767fb-7f22-5dab-aca9-0ec1bfde8399

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Theorems.Thm_LinearMap_finite_and_sum_finrank_eq_of_exact_of_exact_of_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory

namespace ChiColumns

open DoubleComplex

variable {k : Type u} [Field k]

private def _root_.ChiColumns.up (D : Bounded k) : Bounded k where
  C p q := D.C p (q + 1)
  dH p q := D.dH p (q + 1)
  dV p q := D.dV p (q + 1)
  dH_sq p q := D.dH_sq p (q + 1)
  dV_sq p q := D.dV_sq p (q + 1)
  dHV_comm p q := D.dHV_comm p (q + 1)
  N := D.N
  hBound p q h := D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le)

p2m_export "ChiColumns" "up"
variable (D : Bounded k)

def iotaComp {n : ℕ} (i : Diag (n + 1)) : Tot (up D) n →ₗ[k] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(_, 0), _⟩ => 0
  | ⟨(p, q' + 1), h⟩ =>
      LinearMap.proj (R := k) (φ := fun j : Diag n => (up D).C j.1.1 j.1.2) ⟨(p, q'), by omega⟩

def iota (n : ℕ) : Tot (up D) n →ₗ[k] Tot D (n + 1) :=
  LinearMap.pi fun i => iotaComp D i

theorem iota_apply_zero {n p : ℕ} (h : p + 0 = n + 1) (c : Tot (up D) n) :
    iota D n c ⟨(p, 0), h⟩ = 0 := by
  simp only [iota, LinearMap.pi_apply, iotaComp, LinearMap.zero_apply]

theorem iota_apply_succ {n p q' : ℕ} (h : p + (q' + 1) = n + 1) (c : Tot (up D) n) :
    iota D n c ⟨(p, q' + 1), h⟩ = c ⟨(p, q'), by omega⟩ := by
  simp only [iota, LinearMap.pi_apply, iotaComp]; rfl

def proj0 (n : ℕ) : Tot D n →ₗ[k] D.C n 0 :=
  LinearMap.proj (R := k) (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(n, 0), by omega⟩

theorem proj0_apply {n : ℕ} (c : Tot D n) : proj0 D n c = c ⟨(n, 0), by omega⟩ := rfl

theorem dTot_iota (n : ℕ) (c : Tot (up D) n) :
    dTot D (n + 1) (iota D n c) = iota D (n + 1) (dTot (up D) n c) := by
  funext i
  obtain ⟨⟨p, q⟩, h⟩ := i
  cases q with
  | zero =>

    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [iota_apply_zero, dTot_apply_succ_zero, iota_apply_zero, map_zero]
  | succ q' =>
    cases p with
    | zero =>
      obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      rw [dTot_apply_zero_succ, iota_apply_succ, iota_apply_succ, dTot_apply_zero_succ]
      rfl
    | succ p' =>
      rw [dTot_apply_succ_succ, iota_apply_succ, iota_apply_succ]
      cases q' with
      | zero =>
        rw [iota_apply_zero, dTot_apply_succ_zero, map_zero, smul_zero, add_zero]
        rfl
      | succ q'' =>
        rw [iota_apply_succ, dTot_apply_succ_succ]
        rfl

theorem proj0_dTot (n : ℕ) (c : Tot D n) :
    proj0 D (n + 1) (dTot D n c) = D.dH n 0 (proj0 D n c) := by
  rw [proj0_apply, proj0_apply, dTot_apply_succ_zero]

theorem proj0_iota (n : ℕ) (c : Tot (up D) n) : proj0 D (n + 1) (iota D n c) = 0 := by
  rw [proj0_apply, iota_apply_zero]

theorem iota_injective (n : ℕ) : Function.Injective (iota D n) := by
  intro c c' h
  funext i
  obtain ⟨⟨p, q⟩, hi⟩ := i
  have := congrFun h ⟨(p, q + 1), by omega⟩
  rwa [iota_apply_succ, iota_apply_succ] at this

theorem proj0_surjective (n : ℕ) : Function.Surjective (proj0 D n) := by
  classical
  intro x
  refine ⟨Pi.single (⟨(n, 0), by omega⟩ : Diag n) x, ?_⟩
  rw [proj0_apply, Pi.single_eq_same]

theorem ker_proj0_succ (n : ℕ) : LinearMap.ker (proj0 D (n + 1)) = LinearMap.range (iota D n) := by
  apply le_antisymm
  · intro b hb
    rw [LinearMap.mem_ker, proj0_apply] at hb
    refine ⟨fun j => b ⟨(j.1.1, j.1.2 + 1), by have := j.2; omega⟩, ?_⟩
    funext i
    obtain ⟨⟨p, q⟩, hi⟩ := i
    cases q with
    | zero =>
      obtain rfl : p = n + 1 := by omega
      rw [iota_apply_zero]
      exact hb.symm
    | succ q' =>
      rw [iota_apply_succ]
  · rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker, proj0_iota]

theorem proj0_zero_injective : Function.Injective (proj0 D 0) := by
  intro c c' h
  funext i
  obtain ⟨⟨p, q⟩, hi⟩ := i
  obtain rfl : p = 0 := by omega
  obtain rfl : q = 0 := by omega
  rw [proj0_apply, proj0_apply] at h
  exact h

section Bridge

variable (K : CochainComplex (ModuleCat.{u} k) ℕ)

theorem homology_equiv (i j l : ℕ) (hi : (ComplexShape.up ℕ).prev j = i) (hl : (ComplexShape.up ℕ).next j = l) :
    Nonempty ((K.homology j) ≃ₗ[k]
      (LinearMap.ker (K.d j l).hom ⧸ (LinearMap.range (K.d i j).hom).comap (LinearMap.ker (K.d j l).hom).subtype)) := by
  let e1 := (K.homologyIsoSc' i j l hi hl).toLinearEquiv
  let e2 := (K.sc' i j l).moduleCatHomologyIso.toLinearEquiv
  refine ⟨(e1.trans e2).trans (Submodule.quotEquivOfEq _ _ ?_)⟩
  change LinearMap.range ((K.sc' i j l).moduleCatToCycles) = _
  rw [ShortComplex.moduleCatToCycles, LinearMap.range_codRestrict]
  rfl

end Bridge

theorem quot_equiv_of_eq {M N P : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup P] [Module k P] {a a' : M →ₗ[k] N} {b b' : N →ₗ[k] P} (ha : a = a') (hb : b = b') :
    Nonempty ((LinearMap.ker b ⧸ (LinearMap.range a).comap (LinearMap.ker b).subtype) ≃ₗ[k]
      (LinearMap.ker b' ⧸ (LinearMap.range a').comap (LinearMap.ker b').subtype)) := by
  subst ha; subst hb; exact ⟨LinearEquiv.refl k _⟩

theorem quot_equiv_bot_of_eq {M N P : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup P] [Module k P] {a : M →ₗ[k] N} (ha : a = 0) {b b' : N →ₗ[k] P} (hb : b = b') :
    Nonempty ((LinearMap.ker b ⧸ (LinearMap.range a).comap (LinearMap.ker b).subtype) ≃ₗ[k]
      (LinearMap.ker b' ⧸ (⊥ : Submodule k (LinearMap.ker b')))) := by
  subst ha; subst hb
  refine ⟨Submodule.quotEquivOfEq _ _ ?_⟩
  rw [LinearMap.range_zero, Submodule.comap_bot, Submodule.ker_subtype]

noncomputable abbrev Bcx : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (Tot D n)) (fun n => ModuleCat.ofHom (dTot D n))
    (fun n => ModuleCat.hom_ext (by
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, dTot_comp_dTot]; rfl))

noncomputable abbrev Qcx : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (D.C n 0)) (fun n => ModuleCat.ofHom (D.dH n 0))
    (fun n => ModuleCat.hom_ext (by
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, D.dH_sq]; rfl))

def AX : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k PUnit.{u + 1}
  | n + 1 => ModuleCat.of k (Tot (up D) n)

noncomputable def Ad : ∀ n : ℕ, AX D n ⟶ AX D (n + 1)
  | 0 => 0
  | n + 1 => ModuleCat.ofHom (dTot (up D) n)

theorem Ad_sq : ∀ n : ℕ, Ad D n ≫ Ad D (n + 1) = 0
  | 0 => by simp [Ad]
  | n + 1 => by
      show (ModuleCat.ofHom (dTot (up D) n) ≫ ModuleCat.ofHom (dTot (up D) (n + 1)) :
        ModuleCat.of k (Tot (up D) n) ⟶ ModuleCat.of k (Tot (up D) (n + 1 + 1))) = 0
      exact ModuleCat.hom_ext (by
        rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, dTot_comp_dTot]; rfl)

noncomputable abbrev Acx : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (AX D) (Ad D) (Ad_sq D)

theorem Bcx_d (n : ℕ) : (Bcx D).d n (n + 1) = ModuleCat.ofHom (dTot D n) :=
  CochainComplex.of_d (fun n => ModuleCat.of k (Tot D n)) (fun n => ModuleCat.ofHom (dTot D n)) n

theorem Qcx_d (n : ℕ) : (Qcx D).d n (n + 1) = ModuleCat.ofHom (D.dH n 0) :=
  CochainComplex.of_d (fun n => ModuleCat.of k (D.C n 0)) (fun n => ModuleCat.ofHom (D.dH n 0)) n

theorem Acx_d (n : ℕ) : (Acx D).d n (n + 1) = Ad D n :=
  CochainComplex.of_d _ _ n

theorem Acx_d_zero : (Acx D).d 0 1 = 0 := Acx_d D 0

theorem Acx_d_succ (n : ℕ) : (Acx D).d (n + 1) (n + 1 + 1) = ModuleCat.ofHom (dTot (up D) n) :=
  Acx_d D (n + 1)

noncomputable def iotaF : ∀ n : ℕ, (Acx D).X n ⟶ (Bcx D).X n
  | 0 => 0
  | n + 1 => ModuleCat.ofHom (iota D n)

noncomputable def iotaHom : Acx D ⟶ Bcx D :=
  CochainComplex.ofHom (iotaF D) (fun n => by
    cases n with
    | zero =>
      rw [Acx_d]
      simp [iotaF, Ad]
    | succ n =>
      rw [Bcx_d, Acx_d_succ]
      show (ModuleCat.ofHom (iota D n) ≫ ModuleCat.ofHom (dTot D (n + 1)) :
          ModuleCat.of k (Tot (up D) n) ⟶ ModuleCat.of k (Tot D (n + 1 + 1))) =
        ModuleCat.ofHom (dTot (up D) n) ≫ ModuleCat.ofHom (iota D (n + 1))
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
        ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
      apply LinearMap.ext
      intro c
      exact dTot_iota D n c)

noncomputable def projHom : Bcx D ⟶ Qcx D :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (proj0 D n)) (fun n => by
    rw [Bcx_d, Qcx_d]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
      ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
    apply LinearMap.ext
    intro c
    exact (proj0_dTot D n c).symm)

noncomputable def SES : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (iotaHom D) (projHom D) (by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero => simp [iotaHom, iotaF]
    | succ n =>
      simp only [HomologicalComplex.comp_f, iotaHom, projHom, iotaF, HomologicalComplex.zero_f]
      show (ModuleCat.ofHom (iota D n) ≫ ModuleCat.ofHom (proj0 D (n + 1)) :
          ModuleCat.of k (Tot (up D) n) ⟶ ModuleCat.of k (D.C (n + 1) 0)) = 0
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
      apply LinearMap.ext
      intro c
      exact proj0_iota D n c)

theorem SES_shortExact : (SES D).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero =>
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · apply ShortComplex.Exact.moduleCat_of_range_eq_ker
      change LinearMap.range (0 : (AX D 0) →ₗ[k] Tot D 0) = LinearMap.ker (proj0 D 0)
      rw [LinearMap.range_zero, eq_comm, LinearMap.ker_eq_bot]
      exact proj0_zero_injective D
    · change Mono (0 : (Acx D).X 0 ⟶ (Bcx D).X 0)
      haveI : Subsingleton ((Acx D).X 0) := by
        change Subsingleton PUnit
        infer_instance
      exact (ModuleCat.mono_iff_injective _).mpr (fun a b _ => Subsingleton.elim a b)
    · exact (ModuleCat.epi_iff_surjective _).mpr (proj0_surjective D 0)
  | succ n =>
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · apply ShortComplex.Exact.moduleCat_of_range_eq_ker
      exact (ker_proj0_succ D n).symm
    · exact (ModuleCat.mono_iff_injective _).mpr (iota_injective D n)
    · exact (ModuleCat.epi_iff_surjective _).mpr (proj0_surjective D (n + 1))

theorem EB (n : ℕ) : Nonempty ((Bcx D).homology n ≃ₗ[k] HTot D n) := by
  cases n with
  | zero =>
    obtain ⟨e⟩ := homology_equiv (Bcx D) 0 0 (0 + 1) (by simp) (by simp)
    have h0 : ((Bcx D).d 0 0).hom = (0 : Tot D 0 →ₗ[k] Tot D 0) := by
      rw [HomologicalComplex.shape _ _ _ (by simp)]; rfl
    have h1 : ((Bcx D).d 0 (0 + 1)).hom = dTot D 0 := by rw [Bcx_d]; rfl
    obtain ⟨e'⟩ := quot_equiv_bot_of_eq h0 h1
    exact ⟨e.trans e'⟩
  | succ n =>
    obtain ⟨e⟩ := homology_equiv (Bcx D) n (n + 1) (n + 1 + 1) (by simp) (by simp)
    have h0 : ((Bcx D).d n (n + 1)).hom = dTot D n := by rw [Bcx_d]; rfl
    have h1 : ((Bcx D).d (n + 1) (n + 1 + 1)).hom = dTot D (n + 1) := by rw [Bcx_d]; rfl
    obtain ⟨e'⟩ := quot_equiv_of_eq h0 h1
    exact ⟨e.trans e'⟩

theorem EQ (n : ℕ) : Nonempty ((Qcx D).homology n ≃ₗ[k] colH (transpose D) 0 n) := by
  cases n with
  | zero =>
    obtain ⟨e⟩ := homology_equiv (Qcx D) 0 0 (0 + 1) (by simp) (by simp)
    have h0 : ((Qcx D).d 0 0).hom = (0 : D.C 0 0 →ₗ[k] D.C 0 0) := by
      rw [HomologicalComplex.shape _ _ _ (by simp)]; rfl
    have h1 : ((Qcx D).d 0 (0 + 1)).hom = D.dH 0 0 := by rw [Qcx_d]; rfl
    obtain ⟨e'⟩ := quot_equiv_bot_of_eq h0 h1
    exact ⟨e.trans e'⟩
  | succ n =>
    obtain ⟨e⟩ := homology_equiv (Qcx D) n (n + 1) (n + 1 + 1) (by simp) (by simp)
    have h0 : ((Qcx D).d n (n + 1)).hom = D.dH n 0 := by rw [Qcx_d]; rfl
    have h1 : ((Qcx D).d (n + 1) (n + 1 + 1)).hom = D.dH (n + 1) 0 := by rw [Qcx_d]; rfl
    obtain ⟨e'⟩ := quot_equiv_of_eq h0 h1
    exact ⟨e.trans e'⟩

theorem EA (n : ℕ) : Nonempty ((Acx D).homology (n + 1) ≃ₗ[k] HTot (up D) n) := by
  cases n with
  | zero =>
    obtain ⟨e⟩ := homology_equiv (Acx D) 0 (0 + 1) (0 + 1 + 1) (by simp) (by simp)
    have h0 : ((Acx D).d 0 (0 + 1)).hom = (0 : (AX D 0) →ₗ[k] Tot (up D) 0) := by
      rw [Acx_d]; rfl
    have h1 : ((Acx D).d (0 + 1) (0 + 1 + 1)).hom = dTot (up D) 0 := by rw [Acx_d_succ]; rfl
    obtain ⟨e'⟩ := quot_equiv_bot_of_eq h0 h1
    exact ⟨e.trans e'⟩
  | succ n =>
    obtain ⟨e⟩ := homology_equiv (Acx D) (n + 1) (n + 1 + 1) (n + 1 + 1 + 1) (by simp) (by simp)
    have h0 : ((Acx D).d (n + 1) (n + 1 + 1)).hom = dTot (up D) n := by rw [Acx_d_succ]; rfl
    have h1 : ((Acx D).d (n + 1 + 1) (n + 1 + 1 + 1)).hom = dTot (up D) (n + 1) := by rw [Acx_d_succ]; rfl
    obtain ⟨e'⟩ := quot_equiv_of_eq h0 h1
    exact ⟨e.trans e'⟩

theorem A0_subsingleton : Subsingleton ((Acx D).homology 0) := by
  obtain ⟨e⟩ := homology_equiv (Acx D) 0 0 (0 + 1) (by simp) (by simp)
  haveI : Subsingleton ((Acx D).X 0) := by
    change Subsingleton PUnit
    infer_instance
  exact e.toEquiv.subsingleton

theorem subsingleton_HTot_of_forall (X : Bounded k) (m : ℕ)
    (h : ∀ p q : ℕ, p + q = m → Subsingleton (X.C p q)) : Subsingleton (HTot X m) := by
  haveI : ∀ i : Diag m, Subsingleton (X.C i.1.1 i.1.2) := fun i => h _ _ i.2
  haveI : Subsingleton (Tot X m) := inferInstance
  infer_instance

theorem subsingleton_HTot_up_top : Subsingleton (HTot (up D) (2 * D.N - 1)) := by
  apply subsingleton_HTot_of_forall
  intro p q hpq
  change Subsingleton (D.C p (q + 1))
  exact D.hBound p (q + 1) (by omega)

theorem subsingleton_colH_transpose_of (X : Bounded k) (q p : ℕ) (h : Subsingleton (X.C p q)) :
    Subsingleton (colH (transpose X) q p) := by
  haveI : Subsingleton ((transpose X).C q p) := h
  infer_instance

theorem rowPeel
    (hup : ∀ n : ℕ, Module.Finite k (HTot (up D) n))
    (hrow : ∀ p : ℕ, Module.Finite k (colH (transpose D) 0 p)) :
    (∀ n : ℕ, Module.Finite k (HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (HTot D n) : ℤ) =
        ∑ p ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ p * (Module.finrank k (colH (transpose D) 0 p) : ℤ) -
          ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (HTot (up D) n) : ℤ) := by
  classical
  have hS := SES_shortExact D

  let A : ℕ → Type u := fun n => (Acx D).homology n
  let B : ℕ → Type u := fun n => (Bcx D).homology n
  let Q : ℕ → Type u := fun n => (Qcx D).homology n
  let f : ∀ n, A n →ₗ[k] B n := fun n => (HomologicalComplex.homologyMap (SES D).f n).hom
  let g : ∀ n, B n →ₗ[k] Q n := fun n => (HomologicalComplex.homologyMap (SES D).g n).hom
  let δ : ∀ n, Q n →ₗ[k] A (n + 1) := fun n => (hS.δ n (n + 1) rfl).hom
  have hfg : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n) := fun n =>
    (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have hgδ : ∀ n, LinearMap.range (g n) = LinearMap.ker (δ n) := fun n =>
    (hS.homology_exact₃ n (n + 1) rfl).moduleCat_range_eq_ker
  have hδf : ∀ n, LinearMap.range (δ n) = LinearMap.ker (f (n + 1)) := fun n =>
    (hS.homology_exact₁ n (n + 1) rfl).moduleCat_range_eq_ker

  have hA0 : Subsingleton (A 0) := A0_subsingleton D
  have hA : ∀ n, Module.Finite k (A n) := by
    intro n
    cases n with
    | zero => haveI := hA0; infer_instance
    | succ n =>
      obtain ⟨e⟩ := EA D n
      haveI := hup n
      exact Module.Finite.equiv e.symm
  have hQ : ∀ n, Module.Finite k (Q n) := by
    intro n
    obtain ⟨e⟩ := EQ D n
    haveI := hrow n
    exact Module.Finite.equiv e.symm
  have hf0 : Function.Injective (f 0) := fun a b _ => by haveI := hA0; exact Subsingleton.elim a b

  have hAtop : Subsingleton (A (2 * D.N)) := by
    rcases Nat.eq_zero_or_pos D.N with hN | hN
    · have : 2 * D.N = 0 := by omega
      rw [this]; exact hA0
    · obtain ⟨m, hm⟩ : ∃ m, 2 * D.N = m + 1 := ⟨2 * D.N - 1, by omega⟩
      rw [hm]
      obtain ⟨e⟩ := EA D m
      haveI : Subsingleton (HTot (up D) m) := by
        have := subsingleton_HTot_up_top D
        rwa [show 2 * D.N - 1 = m by omega] at this
      exact e.toEquiv.subsingleton
  have hfM : Function.Injective (f (2 * D.N)) := fun a b _ => by
    haveI := hAtop; exact Subsingleton.elim a b
  obtain ⟨hB, hsum⟩ := LinearMap.finite_and_sum_finrank_eq_of_exact_of_exact_of_exact A B Q f g δ
    hfg hgδ hδf hA hQ (2 * D.N) hf0 hfM

  have finB : ∀ n, Module.Finite k (HTot D n) := fun n => by
    obtain ⟨e⟩ := EB D n
    haveI := hB n
    exact Module.Finite.equiv e
  have dB : ∀ n, (Module.finrank k (B n) : ℤ) = Module.finrank k (HTot D n) := fun n => by
    obtain ⟨e⟩ := EB D n; rw [e.finrank_eq]
  have dQ : ∀ n, (Module.finrank k (Q n) : ℤ) = Module.finrank k (colH (transpose D) 0 n) := fun n => by
    obtain ⟨e⟩ := EQ D n; rw [e.finrank_eq]
  have dA0 : (Module.finrank k (A 0) : ℤ) = 0 := by
    haveI := hA0; rw [Module.finrank_zero_of_subsingleton]; rfl
  have dA : ∀ n, (Module.finrank k (A (n + 1)) : ℤ) = Module.finrank k (HTot (up D) n) := fun n => by
    obtain ⟨e⟩ := EA D n; rw [e.finrank_eq]
  refine ⟨finB, ?_⟩
  have sB : ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (B n) : ℤ) =
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (HTot D n) : ℤ) :=
    Finset.sum_congr rfl (fun n _ => by rw [dB n])
  have sQ : ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (Q n) : ℤ) =
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (colH (transpose D) 0 n) : ℤ) :=
    Finset.sum_congr rfl (fun n _ => by rw [dQ n])
  rw [sB, sQ] at hsum
  rcases Nat.eq_zero_or_pos D.N with hN | hN
  · simp [hN]
  · obtain ⟨m, hm⟩ : ∃ m, 2 * D.N = m + 1 := ⟨2 * D.N - 1, by omega⟩
    have htop : (Module.finrank k (HTot (up D) m) : ℤ) = 0 := by
      haveI : Subsingleton (HTot (up D) m) := by
        have := subsingleton_HTot_up_top D
        rwa [show 2 * D.N - 1 = m by omega] at this
      rw [Module.finrank_zero_of_subsingleton]; rfl
    have sA : ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (A n) : ℤ) =
        -∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (HTot (up D) n) : ℤ) := by
      rw [hm, Finset.sum_range_succ', Finset.sum_range_succ, htop, dA0]
      simp only [mul_zero, add_zero, dA]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [sA] at hsum
    rw [hsum]
    ring

end ChiColumns

theorem solution
    {k : Type u} [Field k] (D : DoubleComplex.Bounded k)
    (hup : ∀ n : ℕ, Module.Finite k (DoubleComplex.HTot
        ({ C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
                dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
                dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
                hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) } : DoubleComplex.Bounded k) n))
    (hrow : ∀ p : ℕ, Module.Finite k (DoubleComplex.colH (DoubleComplex.transpose D) 0 p)) :
    (∀ n : ℕ, Module.Finite k (DoubleComplex.HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot D n) : ℤ) =
        ∑ p ∈ Finset.range (2 * D.N),
            (-1 : ℤ) ^ p * (Module.finrank k (DoubleComplex.colH (DoubleComplex.transpose D) 0 p) : ℤ) -
          ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot
            ({ C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
                dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
                dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
                hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) } : DoubleComplex.Bounded k) n) : ℤ) :=
  ChiColumns.rowPeel D hup hrow

end S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift
end P2MW
export P2MW.S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift (solution)
