-- Prove2me | solution 1 for CuspForm.exists_injective_linearMap_torsionBySet_intLattice_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/58157247-b2f2-5478-ba0c-108a7a70e060

import Definitions.Def_CuspForm_LatticeHeckeFamily
import Theorems.Thm_CuspForm_mem_intLattice_iff
import Theorems.Thm_CuspForm_exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le
import Theorems.Thm_CuspForm_qCoeff_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_injective_linearMap_torsionBySet_intLattice_quotient

set_option autoImplicit false
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

namespace HeckeFirstCoefficient

private theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine Subgroup.mem_map.mpr ⟨ModularGroup.T, ?_, ?_⟩
  · rw [Gamma0_mem]
    simp [ModularGroup.T]
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom,
        Matrix.SpecialLinearGroup.mapGL]

variable {N : ℕ}

private theorem _root_.HeckeFirstCoefficient.qCoeff_zero (j : ℕ) :
    ModularFormClass.qCoeff (0 : CuspForm (Gamma0 N) 2) j = 0 := by
  simp only [ModularFormClass.qCoeff, CuspForm.coe_zero, qExpansion_zero, map_zero]

p2m_export "HeckeFirstCoefficient" "qCoeff_zero"
private theorem qCoeff_add (g h : CuspForm (Gamma0 N) 2) (j : ℕ) :
    ModularFormClass.qCoeff (⇑(g + h)) j =
      ModularFormClass.qCoeff g j + ModularFormClass.qCoeff h j := by
  simp only [ModularFormClass.qCoeff, CuspForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) g h, map_add]

private theorem qCoeff_sub (g h : CuspForm (Gamma0 N) 2) (j : ℕ) :
    ModularFormClass.qCoeff (⇑(g - h)) j =
      ModularFormClass.qCoeff g j - ModularFormClass.qCoeff h j := by
  simp only [ModularFormClass.qCoeff, CuspForm.coe_sub,
    ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods N) g h, map_sub]

end HeckeFirstCoefficient

private theorem coeffTranslate (N : ℕ) [NeZero N] (n : ℕ) :
    ∃ t ∈ CuspForm.heckeAlgebra N 2 ∅, ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ModularFormClass.qCoeff (t f) 1 = ModularFormClass.qCoeff f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, zero_mem _, fun f => by
      rw [LinearMap.zero_apply, HeckeFirstCoefficient.qCoeff_zero, CuspForm.qCoeff_zero f]⟩
  · exact CuspForm.exists_mem_heckeAlgebra_qCoeff_one_eq_qCoeff_of_one_le N 2 (by norm_num) n hn

namespace FirstCoefficientSeparation

private theorem addMonoidHom_field_int_apply_eq_zero {K : Type*} [Field K] (φ : K →+ ℤ) (c : K) :
    φ c = 0 := by
  have hdvd : ∀ n : ℕ, 0 < n → ((n : ℕ) : ℤ) ∣ φ c := by
    intro n hn
    by_cases hnK : ((n : ℕ) : K) = 0
    · have h1 : n • φ c = 0 := by
        rw [← map_nsmul, nsmul_eq_mul, hnK, zero_mul, map_zero]
      have h2 : φ c = 0 := by
        rw [nsmul_eq_mul] at h1
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd (by exact_mod_cast h) (by omega : n ≠ 0)
        · exact h
      rw [h2]; exact dvd_zero _
    · refine ⟨φ (((n : ℕ) : K)⁻¹ * c), ?_⟩
      have h1 : c = n • (((n : ℕ) : K)⁻¹ * c) := by
        rw [nsmul_eq_mul, mul_inv_cancel_left₀ hnK]
      conv_lhs => rw [h1]
      rw [map_nsmul, nsmul_eq_mul]
  exact Int.eq_zero_of_abs_lt_dvd (hdvd ((φ c).natAbs + 1) (Nat.succ_pos _)) (by simp)

private theorem finrank_le_one_of_injective_dual {k : Type*} [Field k] [Finite k] {q : ℕ}
    [Fact q.Prime] [Module (ZMod q) k] {V : Type*} [AddCommGroup V] [Module k V] [Finite V]
    (Ψ : V → Module.Dual (ZMod q) k) (hΨ : Function.Injective Ψ) : Module.finrank k V ≤ 1 := by
  haveI : Module.Finite k V := Module.Finite.of_finite
  haveI : Module.Finite (ZMod q) k := Module.Finite.of_finite
  have hcardV : Nat.card V = Nat.card k ^ Module.finrank k V := Module.natCard_eq_pow_finrank
  have hcardk : Nat.card k = Nat.card (ZMod q) ^ Module.finrank (ZMod q) k :=
    Module.natCard_eq_pow_finrank
  have hcardD : Nat.card (Module.Dual (ZMod q) k) =
      Nat.card (ZMod q) ^ Module.finrank (ZMod q) (Module.Dual (ZMod q) k) :=
    Module.natCard_eq_pow_finrank
  rw [Subspace.dual_finrank_eq, ← hcardk] at hcardD
  have hle : Nat.card V ≤ Nat.card (Module.Dual (ZMod q) k) := by
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    haveI : Finite (Module.Dual (ZMod q) k) := Module.finite_of_finite (ZMod q)
    exact Nat.card_le_card_of_injective Ψ hΨ
  rw [hcardD, hcardV] at hle
  have hk : 1 < Nat.card k := Finite.one_lt_card
  conv_rhs at hle => rw [← pow_one (Nat.card k)]
  exact (Nat.pow_le_pow_iff_right hk).mp hle

private theorem exists_injective_of_finrank_le_one {k : Type*} [Field k] {V : Type*}
    [AddCommGroup V] [Module k V] [Module.Finite k V] (h : Module.finrank k V ≤ 1) :
    ∃ a : V →ₗ[k] k, Function.Injective a := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact ⟨0, Function.injective_of_subsingleton _⟩
  · refine ⟨(LinearEquiv.ofFinrankEq V k ?_).toLinearMap, LinearEquiv.injective _⟩
    rw [h1, Module.finrank_self]

end FirstCoefficientSeparation

namespace FirstCoefficientSeparation

open CuspForm ModularCurve

section Carrier

variable (N : ℕ)

private theorem qCoeff_coe_nsmul (p : ℕ) (f : ↥(intLattice N 2)) (n : ℕ) :
    ModularFormClass.qCoeff ((p • f : ↥(intLattice N 2)) : CuspForm (Gamma0 N) 2) n =
      (p : ℂ) * ModularFormClass.qCoeff (f : CuspForm (Gamma0 N) 2) n := by
  induction p with
  | zero => simp only [zero_nsmul, ZeroMemClass.coe_zero, HeckeFirstCoefficient.qCoeff_zero,
      Nat.cast_zero, zero_mul]
  | succ p ih =>
    rw [succ_nsmul, Submodule.coe_add, HeckeFirstCoefficient.qCoeff_add, ih, Nat.cast_succ,
      add_mul, one_mul]

private theorem qCoeff_coe_sub (f g : ↥(intLattice N 2)) (n : ℕ) :
    ModularFormClass.qCoeff ((f - g : ↥(intLattice N 2)) : CuspForm (Gamma0 N) 2) n =
      ModularFormClass.qCoeff (f : CuspForm (Gamma0 N) 2) n -
        ModularFormClass.qCoeff (g : CuspForm (Gamma0 N) 2) n := by
  rw [Submodule.coe_sub, HeckeFirstCoefficient.qCoeff_sub]

private theorem exists_int_qCoeff (f : ↥(intLattice N 2)) (n : ℕ) :
    ∃ z : ℤ, ModularFormClass.qCoeff (f : CuspForm (Gamma0 N) 2) n = (z : ℂ) :=
  (mem_intLattice_iff (f : CuspForm (Gamma0 N) 2)).mp f.2 n

private noncomputable def intCoeff (f : ↥(intLattice N 2)) (n : ℕ) : ℤ :=
  Classical.choose (exists_int_qCoeff N f n)

private theorem intCoeff_spec (f : ↥(intLattice N 2)) (n : ℕ) :
    ModularFormClass.qCoeff (f : CuspForm (Gamma0 N) 2) n = (intCoeff N f n : ℂ) :=
  Classical.choose_spec (exists_int_qCoeff N f n)

private theorem intCoeff_eq_of_qCoeff_eq {f g : ↥(intLattice N 2)} {a b : ℕ}
    (h : ModularFormClass.qCoeff (f : CuspForm (Gamma0 N) 2) a =
      ModularFormClass.qCoeff (g : CuspForm (Gamma0 N) 2) b) :
    intCoeff N f a = intCoeff N g b := by
  have := h
  rw [intCoeff_spec, intCoeff_spec] at this
  exact_mod_cast this

private theorem intCoeff_nsmul (p : ℕ) (f : ↥(intLattice N 2)) (n : ℕ) :
    intCoeff N (p • f) n = (p : ℤ) * intCoeff N f n := by
  have h := qCoeff_coe_nsmul N p f n
  rw [intCoeff_spec, intCoeff_spec] at h
  exact_mod_cast h

private theorem intCoeff_zero (n : ℕ) : intCoeff N 0 n = 0 := by
  have h := intCoeff_spec N 0 n
  rw [ZeroMemClass.coe_zero, HeckeFirstCoefficient.qCoeff_zero] at h
  exact_mod_cast h.symm

private theorem intCoeff_add (f g : ↥(intLattice N 2)) (n : ℕ) :
    intCoeff N (f + g) n = intCoeff N f n + intCoeff N g n := by
  have h := intCoeff_spec N (f + g) n
  rw [Submodule.coe_add, HeckeFirstCoefficient.qCoeff_add, intCoeff_spec, intCoeff_spec] at h
  exact_mod_cast h.symm

private theorem intCoeff_sub (f g : ↥(intLattice N 2)) (n : ℕ) :
    intCoeff N (f - g) n = intCoeff N f n - intCoeff N g n := by
  have h := qCoeff_coe_sub N f g n
  rw [intCoeff_spec, intCoeff_spec, intCoeff_spec] at h
  exact_mod_cast h

variable [NeZero N]

private theorem eq_zero_of_forall_intCoeff_eq_zero {f : ↥(intLattice N 2)}
    (h : ∀ n, intCoeff N f n = 0) : f = 0 := by
  apply Subtype.ext
  apply DFunLike.coe_injective
  have h1 : (1 : ℝ) ∈ (Gamma0 N).strictPeriods := HeckeFirstCoefficient.one_mem_strictPeriods N
  have hq : qExpansion 1 (f : CuspForm (Gamma0 N) 2) = 0 := by
    ext n
    have := intCoeff_spec N f n
    rw [h n, Int.cast_zero] at this
    simpa [ModularFormClass.qCoeff] using this
  have := (qExpansion_eq_zero_iff one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex (f : CuspForm (Gamma0 N) 2) h1)
    (ModularFormClass.holo (f : CuspForm (Gamma0 N) 2))
    (ModularFormClass.bdd_at_infty (f : CuspForm (Gamma0 N) 2))).mp hq
  simpa using this

private noncomputable scoped instance latMod : Module HeckeAlg ↥(intLattice N 2) :=
  (latticeHeckeFamily N).module

private noncomputable scoped instance latSMul : SMul HeckeAlg ↥(intLattice N 2) :=
  (latMod N).toDistribMulAction.toMulAction.toSMul

private theorem smul_def (s : HeckeAlg) (f : ↥(intLattice N 2)) :
    s • f = (latticeHeckeFamily N).endHom s f := rfl

private theorem natCast_smul_eq (p : ℕ) (f : ↥(intLattice N 2)) :
    ((p : ℕ) : HeckeAlg) • f = p • f := by
  rw [smul_def, map_natCast, Module.End.natCast_apply]

private noncomputable def pL (p : ℕ) : Submodule HeckeAlg ↥(intLattice N 2) :=
  Ideal.span {((p : ℕ) : HeckeAlg)} • (⊤ : Submodule HeckeAlg ↥(intLattice N 2))

private noncomputable scoped instance quotMulAction (p : ℕ) :
    MulAction HeckeAlg (↥(intLattice N 2) ⧸ pL N p) :=
  (inferInstance : Module HeckeAlg (↥(intLattice N 2) ⧸ pL N p)).toDistribMulAction.toMulAction

private noncomputable scoped instance quotDistribMulAction (p : ℕ) :
    DistribMulAction HeckeAlg (↥(intLattice N 2) ⧸ pL N p) :=
  (inferInstance : Module HeckeAlg (↥(intLattice N 2) ⧸ pL N p)).toDistribMulAction

private theorem nsmul_mem_pL (p : ℕ) (g : ↥(intLattice N 2)) : p • g ∈ pL N p := by
  rw [← natCast_smul_eq]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

private theorem exists_eq_nsmul_of_mem_pL {p : ℕ} {x : ↥(intLattice N 2)} (hx : x ∈ pL N p) :
    ∃ g : ↥(intLattice N 2), x = p • g := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr n _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    refine ⟨c • n, ?_⟩
    rw [mul_smul, natCast_smul_eq, smul_comm]
  · rintro x y ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g + g', (nsmul_add g g' p).symm⟩

private theorem dvd_intCoeff_of_mem_pL {p : ℕ} {x : ↥(intLattice N 2)} (hx : x ∈ pL N p) (n : ℕ) :
    (p : ℤ) ∣ intCoeff N x n := by
  obtain ⟨g, rfl⟩ := exists_eq_nsmul_of_mem_pL N hx
  rw [intCoeff_nsmul]
  exact dvd_mul_right _ _

private theorem mem_pL_of_forall_dvd {p : ℕ} (hp : p ≠ 0) {f : ↥(intLattice N 2)}
    (h : ∀ n, (p : ℤ) ∣ intCoeff N f n) : f ∈ pL N p := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have h1 : (1 : ℝ) ∈ (Gamma0 N).strictPeriods := HeckeFirstCoefficient.one_mem_strictPeriods N
  set g₀ : CuspForm (Gamma0 N) 2 := ((p : ℂ)⁻¹) • (f : CuspForm (Gamma0 N) 2) with hg₀
  have hcoeff : ∀ n, ModularFormClass.qCoeff g₀ n =
      (p : ℂ)⁻¹ * ModularFormClass.qCoeff (f : CuspForm (Gamma0 N) 2) n := by
    intro n
    simp only [hg₀, ModularFormClass.qCoeff, CuspForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos h1, map_smul, smul_eq_mul]
  have hg₀mem : g₀ ∈ intLattice N 2 := by
    rw [mem_intLattice_iff]
    intro n
    obtain ⟨z, hz⟩ := h n
    refine ⟨z, ?_⟩
    rw [hcoeff, intCoeff_spec, hz, Int.cast_mul, Int.cast_natCast, inv_mul_cancel_left₀ hpC]
  have hfg : f = p • (⟨g₀, hg₀mem⟩ : ↥(intLattice N 2)) := by
    apply Subtype.ext
    change (f : CuspForm (Gamma0 N) 2) = ((p • (⟨g₀, hg₀mem⟩ : ↥(intLattice N 2)) :
      ↥(intLattice N 2)) : CuspForm (Gamma0 N) 2)
    rw [AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
    simp only [hg₀, smul_smul, mul_inv_cancel₀ hpC, one_smul]
  rw [hfg]
  exact nsmul_mem_pL N p _

private theorem exists_endHom_eq {t : Module.End ℂ (CuspForm (Gamma0 N) 2)}
    (ht : t ∈ heckeAlgebra N 2 ∅) :
    ∃ s : HeckeAlg, (latticeHeckeFamily N).endHom s = latticeActionHom N ∅ ⟨t, ht⟩ := by
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨ℓ, hℓN, hℓ, -, rfl⟩
    · refine ⟨heckeGen ⟨ℓ, hℓ⟩, ?_⟩
      rw [CommutingHeckeFamily.endHom_heckeGen, latticeHeckeFamily_T,
        heckeAlgebra.atPrime_of_not_dvd N (ℓ := ⟨ℓ, hℓ⟩) hℓN]
      rfl
    · refine ⟨heckeGen ⟨ℓ, hℓ⟩, ?_⟩
      rw [CommutingHeckeFamily.endHom_heckeGen, latticeHeckeFamily_T,
        heckeAlgebra.atPrime_of_dvd N (ℓ := ⟨ℓ, hℓ⟩) hℓN]
      rfl
  | algebraMap r =>
    refine ⟨(r : HeckeAlg), ?_⟩
    have h1 : (⟨algebraMap ℤ (Module.End ℂ (CuspForm (Gamma0 N) 2)) r, Subalgebra.algebraMap_mem _ r⟩ :
        ↥(heckeAlgebra N 2 ∅)) = (r : ↥(heckeAlgebra N 2 ∅)) := by
      apply Subtype.ext
      simp
    rw [map_intCast, h1, map_intCast]
  | add x y hx hy ihx ihy =>
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨s', hs'⟩ := ihy
    refine ⟨s + s', ?_⟩
    have h1 : (⟨x + y, add_mem hx hy⟩ : ↥(heckeAlgebra N 2 ∅)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [RingHom.map_add (latticeHeckeFamily N).endHom, hs, hs', h1, RingHom.map_add (latticeActionHom N ∅)]
  | mul x y hx hy ihx ihy =>
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨s', hs'⟩ := ihy
    refine ⟨s * s', ?_⟩
    have h1 : (⟨x * y, mul_mem hx hy⟩ : ↥(heckeAlgebra N 2 ∅)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [RingHom.map_mul (latticeHeckeFamily N).endHom, hs, hs', h1, RingHom.map_mul (latticeActionHom N ∅)]

private theorem coe_latticeActionHom_apply {t : Module.End ℂ (CuspForm (Gamma0 N) 2)}
    (ht : t ∈ heckeAlgebra N 2 ∅) (f : ↥(intLattice N 2)) :
    ((latticeActionHom N ∅ ⟨t, ht⟩ f : ↥(intLattice N 2)) : CuspForm (Gamma0 N) 2) =
      t (f : CuspForm (Gamma0 N) 2) := rfl

private theorem exists_intCoeff_eq (n : ℕ) :
    ∃ s : HeckeAlg, ∀ f : ↥(intLattice N 2), intCoeff N f n = intCoeff N (s • f) 1 := by
  obtain ⟨t, ht, htf⟩ := coeffTranslate N n
  obtain ⟨s, hs⟩ := exists_endHom_eq N ht
  refine ⟨s, fun f => ?_⟩
  apply intCoeff_eq_of_qCoeff_eq
  rw [smul_def, hs, coe_latticeActionHom_apply, htf]

variable (p : ℕ) (m : Ideal HeckeAlg)

private theorem smul_mem_pL_of_mem_torsion {x : ↥(intLattice N 2) ⧸ pL N p}
    (hx : x ∈ Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m)
    {f : ↥(intLattice N 2)} (hf : Submodule.Quotient.mk f = x) {s : HeckeAlg} (hs : s ∈ m) :
    s • f ∈ pL N p := by
  rw [Submodule.mem_torsionBySet_iff] at hx
  have := hx ⟨s, hs⟩
  rw [← hf, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  exact this

private theorem eq_zero_of_forall_dvd (hp : p ≠ 0) {x : ↥(intLattice N 2) ⧸ pL N p}
    {f : ↥(intLattice N 2)} (hf : Submodule.Quotient.mk f = x)
    (h : ∀ s : HeckeAlg, (p : ℤ) ∣ intCoeff N (s • f) 1) : x = 0 := by
  rw [← hf, Submodule.Quotient.mk_eq_zero]
  refine mem_pL_of_forall_dvd N hp fun n => ?_
  obtain ⟨s, hs⟩ := exists_intCoeff_eq N n
  rw [hs f]
  exact h s

private theorem eq_zero_of_mem_torsion_zero [m.IsMaximal] {x : ↥(intLattice N 2) ⧸ pL N 0}
    (hx : x ∈ Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N 0) m) : x = 0 := by
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ x

  have hkill : ∀ s ∈ m, s • f = 0 := by
    intro s hs
    obtain ⟨g, hg⟩ := exists_eq_nsmul_of_mem_pL N (smul_mem_pL_of_mem_torsion N 0 m hx hf hs)
    rw [hg, zero_nsmul]
  have hcongr : ∀ s s' : HeckeAlg, Ideal.Quotient.mk m s = Ideal.Quotient.mk m s' →
      intCoeff N (s • f) 1 = intCoeff N (s' • f) 1 := by
    intro s s' hss'
    have h1 : (s - s') • f = 0 := hkill _ (Ideal.Quotient.eq.mp hss')
    rw [sub_smul, sub_eq_zero] at h1
    rw [h1]
  letI : Field (HeckeAlg ⧸ m) := Ideal.Quotient.field m
  let lift : HeckeAlg ⧸ m → HeckeAlg := fun c => Classical.choose (Ideal.Quotient.mk_surjective c)
  have hlift : ∀ c, Ideal.Quotient.mk m (lift c) = c :=
    fun c => Classical.choose_spec (Ideal.Quotient.mk_surjective c)
  let φ : HeckeAlg ⧸ m →+ ℤ :=
    { toFun := fun c => intCoeff N (lift c • f) 1
      map_zero' := by
        have h0 : intCoeff N (lift 0 • f) 1 = intCoeff N ((0 : HeckeAlg) • f) 1 :=
          hcongr _ _ (by rw [hlift, map_zero])
        rw [h0, zero_smul, intCoeff_zero]
      map_add' := by
        intro c d
        have h1 : intCoeff N (lift (c + d) • f) 1 = intCoeff N ((lift c + lift d) • f) 1 :=
          hcongr _ _ (by rw [hlift, map_add, hlift, hlift])
        rw [h1, add_smul, intCoeff_add] }
  have hφ : ∀ s : HeckeAlg, intCoeff N (s • f) 1 = 0 := by
    intro s
    have h1 : φ (Ideal.Quotient.mk m s) = 0 := addMonoidHom_field_int_apply_eq_zero φ _
    have h2 : φ (Ideal.Quotient.mk m s) = intCoeff N (lift (Ideal.Quotient.mk m s) • f) 1 := rfl
    rw [h2, hcongr _ s (hlift _)] at h1
    exact h1
  have hf0 : f = 0 := by
    refine eq_zero_of_forall_intCoeff_eq_zero N fun n => ?_
    obtain ⟨s, hs⟩ := exists_intCoeff_eq N n
    rw [hs f, hφ]
  rw [← hf, hf0, Submodule.Quotient.mk_eq_zero]
  exact Submodule.zero_mem _

private theorem finite_quotient (hp : p ≠ 0) : Finite (↥(intLattice N 2) ⧸ pL N p) := by
  haveI : Module.Finite ℤ ↥(intLattice N 2) := intLattice.moduleFinite N
  haveI : AddGroup.FG ↥(intLattice N 2) := Module.Finite.iff_addGroup_fg.mp inferInstance
  haveI : AddGroup.FG (↥(intLattice N 2) ⧸ pL N p) :=
    AddGroup.fg_of_surjective (f := (pL N p).mkQ.toAddMonoidHom) (Submodule.mkQ_surjective _)
  refine AddCommGroup.finite_of_fg_torsion (G := ↥(intLattice N 2) ⧸ pL N p) fun x => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p, Nat.pos_of_ne_zero hp, ?_⟩
  show p • (pL N p).mkQ f = 0
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact nsmul_mem_pL N p f

private theorem r_dvd_intCoeff (hp : p ≠ 0) {q r : ℕ} (hpr : p = q * r)
    (hqm : ((q : ℕ) : HeckeAlg) ∈ m) {x : ↥(intLattice N 2) ⧸ pL N p}
    (hx : x ∈ Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m)
    {f : ↥(intLattice N 2)} (hf : Submodule.Quotient.mk f = x) (n : ℕ) :
    ((r : ℕ) : ℤ) ∣ intCoeff N f n := by
  obtain ⟨g, hg⟩ := exists_eq_nsmul_of_mem_pL N (smul_mem_pL_of_mem_torsion N p m hx hf hqm)
  rw [natCast_smul_eq] at hg
  have h2 : intCoeff N (q • f) n = intCoeff N (p • g) n := by rw [hg]
  rw [intCoeff_nsmul, intCoeff_nsmul, hpr, Nat.cast_mul, mul_assoc] at h2
  have hq0 : ((q : ℕ) : ℤ) ≠ 0 := by
    have : q ≠ 0 := fun h => hp (by rw [hpr, h, zero_mul])
    exact_mod_cast this
  exact ⟨intCoeff N g n, mul_left_cancel₀ hq0 h2⟩

private theorem finrank_le_one_of_nontrivial (hp : p ≠ 0) [m.IsMaximal]
    (hpm : ((p : ℕ) : HeckeAlg) ∈ m)
    (hV : Nontrivial ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m)) :
    letI : Field (HeckeAlg ⧸ m) := Ideal.Quotient.field m
    Module.finrank (HeckeAlg ⧸ m)
      ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m) ≤ 1 := by
  letI : Field (HeckeAlg ⧸ m) := Ideal.Quotient.field m
  haveI : Finite (↥(intLattice N 2) ⧸ pL N p) := finite_quotient N p hp

  haveI := hV
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m))

  have hfin_k : Finite (HeckeAlg ⧸ m) := by
    let lk : HeckeAlg ⧸ m → HeckeAlg := fun c => Classical.choose (Ideal.Quotient.mk_surjective c)
    have hlk : ∀ c, Ideal.Quotient.mk m (lk c) = c :=
      fun c => Classical.choose_spec (Ideal.Quotient.mk_surjective c)
    refine Finite.of_injective (fun c => lk c • v₀.1) fun c d hcd => ?_
    by_contra hne
    have hr : Ideal.Quotient.mk m (lk c - lk d) ≠ 0 := by
      rw [map_sub, hlk, hlk]; exact sub_ne_zero.mpr hne
    have hrv : (lk c - lk d) • v₀.1 = 0 := by
      rw [sub_smul]; exact sub_eq_zero.mpr hcd
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk m (lk c - lk d))⁻¹
    have hunit : u * (lk c - lk d) - 1 ∈ m := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hu, inv_mul_cancel₀ hr, sub_self]
    have hx := v₀.2
    rw [Submodule.mem_torsionBySet_iff] at hx
    have h1 : (u * (lk c - lk d) - 1) • v₀.1 = 0 := hx ⟨_, hunit⟩
    rw [sub_smul, one_smul, mul_smul, hrv, smul_zero, zero_sub, neg_eq_zero] at h1
    exact hv₀ (Subtype.ext h1)
  haveI := hfin_k

  obtain ⟨q, hqchar⟩ : ∃ q : ℕ, CharP (HeckeAlg ⧸ m) q := ⟨_, ringChar.charP _⟩
  have hq0 : q ≠ 0 := CharP.char_ne_zero_of_finite (HeckeAlg ⧸ m) q
  have hq : q.Prime := (CharP.char_is_prime_or_zero (HeckeAlg ⧸ m) q).resolve_right hq0
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq0⟩
  have hpk : ((p : ℕ) : HeckeAlg ⧸ m) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
    exact hpm
  obtain ⟨r, hpr⟩ : q ∣ p := (CharP.cast_eq_zero_iff (HeckeAlg ⧸ m) q p).mp hpk
  have hqm : ((q : ℕ) : HeckeAlg) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (HeckeAlg ⧸ m) q
  have hr0 : ((r : ℕ) : ℤ) ≠ 0 := by
    have : r ≠ 0 := fun h => hp (by rw [hpr, h, mul_zero])
    exact_mod_cast this
  letI : Module (ZMod q) (HeckeAlg ⧸ m) := AddCommGroup.zmodModule (fun x => by
    rw [nsmul_eq_mul, CharP.cast_eq_zero (HeckeAlg ⧸ m) q, zero_mul])

  let lift : ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m) →
      ↥(intLattice N 2) := fun v => Classical.choose (Submodule.Quotient.mk_surjective _ v.1)
  have hlift : ∀ v, Submodule.Quotient.mk (p := pL N p) (lift v) = v.1 :=
    fun v => Classical.choose_spec (Submodule.Quotient.mk_surjective _ v.1)
  let liftk : HeckeAlg ⧸ m → HeckeAlg := fun c => Classical.choose (Ideal.Quotient.mk_surjective c)
  have hliftk : ∀ c, Ideal.Quotient.mk m (liftk c) = c :=
    fun c => Classical.choose_spec (Ideal.Quotient.mk_surjective c)

  have hdvd : ∀ v (s : HeckeAlg), ((r : ℕ) : ℤ) ∣ intCoeff N (s • lift v) 1 := by
    intro v s
    refine r_dvd_intCoeff N p m hp hpr hqm (x := s • v.1) (Submodule.smul_mem _ s v.2) ?_ 1
    rw [Submodule.Quotient.mk_smul, hlift]
  let A : ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m) → HeckeAlg → ℤ :=
    fun v s => Classical.choose (hdvd v s)
  have hA : ∀ v s, intCoeff N (s • lift v) 1 = ((r : ℕ) : ℤ) * A v s :=
    fun v s => Classical.choose_spec (hdvd v s)
  have hA_add : ∀ v (s s' : HeckeAlg), A v (s + s') = A v s + A v s' := by
    intro v s s'
    apply mul_left_cancel₀ hr0
    rw [← hA, add_smul, intCoeff_add, hA, hA, mul_add]
  have hA_congr : ∀ v (s s' : HeckeAlg), s - s' ∈ m → ((q : ℕ) : ℤ) ∣ A v s - A v s' := by
    intro v s s' hss'
    have h1 : (p : ℤ) ∣ intCoeff N ((s - s') • lift v) 1 :=
      dvd_intCoeff_of_mem_pL N (smul_mem_pL_of_mem_torsion N p m v.2 (hlift v) hss') 1
    rw [sub_smul, intCoeff_sub, hA, hA, ← mul_sub, hpr, Nat.cast_mul, mul_comm ((q : ℕ) : ℤ)] at h1
    exact (mul_dvd_mul_iff_left hr0).mp h1

  let ψ : ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m) →
      (HeckeAlg ⧸ m) →+ ZMod q := fun v =>
    AddMonoidHom.mk' (fun c => ((A v (liftk c) : ℤ) : ZMod q)) (by
      intro c d
      have h1 : ((q : ℕ) : ℤ) ∣ A v (liftk (c + d)) - A v (liftk c + liftk d) :=
        hA_congr v _ _ (Ideal.Quotient.eq.mp (by rw [hliftk, map_add, hliftk, hliftk]))
      rw [hA_add] at h1
      have h2 : ((A v (liftk (c + d)) - (A v (liftk c) + A v (liftk d)) : ℤ) : ZMod q) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h1
      rw [Int.cast_sub, Int.cast_add, sub_eq_zero] at h2
      exact h2)
  let Ψ : ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m) →
      Module.Dual (ZMod q) (HeckeAlg ⧸ m) := fun v => AddMonoidHom.toZModLinearMap q (ψ v)
  have hΨ : Function.Injective Ψ := by
    intro v w hvw
    have hψ : ∀ c, ((A v (liftk c) : ℤ) : ZMod q) = ((A w (liftk c) : ℤ) : ZMod q) :=
      fun c => LinearMap.congr_fun hvw c

    have hqs : ∀ s : HeckeAlg, ((q : ℕ) : ℤ) ∣ A v s - A w s := by
      intro s
      have hmem : liftk (Ideal.Quotient.mk m s) - s ∈ m := Ideal.Quotient.eq.mp (by rw [hliftk])
      have h1 := hA_congr v _ _ hmem
      have h3 := hA_congr w _ _ hmem
      have h2 : ((q : ℕ) : ℤ) ∣ A v (liftk (Ideal.Quotient.mk m s)) - A w (liftk (Ideal.Quotient.mk m s)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
        exact hψ _
      have : A v s - A w s = (A v (liftk (Ideal.Quotient.mk m s)) - A w (liftk (Ideal.Quotient.mk m s)))
          - (A v (liftk (Ideal.Quotient.mk m s)) - A v s)
          + (A w (liftk (Ideal.Quotient.mk m s)) - A w s) := by ring
      rw [this]
      exact dvd_add (dvd_sub h2 h1) h3

    have hsep : v.1 - w.1 = (0 : ↥(intLattice N 2) ⧸ pL N p) := by
      refine eq_zero_of_forall_dvd N p hp (f := lift v - lift w) ?_ fun s => ?_
      · rw [Submodule.Quotient.mk_sub, hlift, hlift]
      · obtain ⟨e, he⟩ := hqs s
        refine ⟨e, ?_⟩
        rw [smul_sub, intCoeff_sub, hA, hA, ← mul_sub, he, hpr, Nat.cast_mul]
        ring
    exact Subtype.ext (sub_eq_zero.mp hsep)
  exact finrank_le_one_of_injective_dual Ψ hΨ

private theorem main_result [m.IsMaximal] (hpm : ((p : ℕ) : HeckeAlg) ∈ m) :
    ∃ a : ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m)
        →ₗ[HeckeAlg ⧸ m] (HeckeAlg ⧸ m), Function.Injective a := by
  letI : Field (HeckeAlg ⧸ m) := Ideal.Quotient.field m
  rcases subsingleton_or_nontrivial
    ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m) with hsub | hV
  · haveI := hsub
    exact ⟨0, Function.injective_of_subsingleton _⟩
  · rcases Nat.eq_zero_or_pos p with hp0 | hppos
    ·
      exfalso
      subst hp0
      obtain ⟨v, w, hvw⟩ := hV.exists_pair_ne
      apply hvw
      apply Subtype.ext
      rw [eq_zero_of_mem_torsion_zero N m v.2, eq_zero_of_mem_torsion_zero N m w.2]
    · haveI : Finite (↥(intLattice N 2) ⧸ pL N p) := finite_quotient N p hppos.ne'
      haveI : Module.Finite (HeckeAlg ⧸ m)
          ↥(Submodule.torsionBySet HeckeAlg (↥(intLattice N 2) ⧸ pL N p) m) :=
        Module.Finite.of_finite
      exact exists_injective_of_finrank_le_one
        (finrank_le_one_of_nontrivial N p m hppos.ne' hpm hV)

end Carrier

end FirstCoefficientSeparation
p2m_reactivate "P2MW.S_CuspForm_exists_injective_linearMap_torsionBySet_intLattice_quotient.FirstCoefficientSeparation"

open FirstCoefficientSeparation in

theorem solution (N p : ℕ) [NeZero N]
    (m : Ideal ModularCurve.HeckeAlg) [m.IsMaximal] (hpm : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ m) :
    letI := (CuspForm.latticeHeckeFamily N).module
    ∃ a : Submodule.torsionBySet ModularCurve.HeckeAlg
        (↥(CuspForm.intLattice N 2) ⧸ (Ideal.span {((p : ℕ) : ModularCurve.HeckeAlg)} • (⊤ : Submodule ModularCurve.HeckeAlg ↥(CuspForm.intLattice N 2)))) m
          →ₗ[ModularCurve.HeckeAlg ⧸ m] (ModularCurve.HeckeAlg ⧸ m),
      Function.Injective a :=
  FirstCoefficientSeparation.main_result _ _ _ hpm

end
end S_CuspForm_exists_injective_linearMap_torsionBySet_intLattice_quotient
end P2MW
export P2MW.S_CuspForm_exists_injective_linearMap_torsionBySet_intLattice_quotient (solution)
