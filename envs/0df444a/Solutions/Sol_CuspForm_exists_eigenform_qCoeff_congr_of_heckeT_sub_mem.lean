-- Prove2me | solution 1 for CuspForm.exists_eigenform_qCoeff_congr_of_heckeT_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ec772e54-2a8a-58c2-a06f-c5646366a601

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_CuspForm_finiteDimensional_cuspForm
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_heckeTLin_comm
import Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm
import Theorems.Thm_DeligneSerre_exists_charZero_eigenvector_of_residual_character
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_eigenform_qCoeff_congr_of_heckeT_sub_mem

set_option autoImplicit false

open CuspForm ModularFormClass
open scoped IsMulCommutative

namespace RC1

private lemma restrict_commute {Φ : Type} [AddCommGroup Φ] [Module ℂ Φ]
    (L : Submodule ℤ Φ) (a b : Module.End ℂ Φ)
    (ha : ∀ g ∈ L, a g ∈ L) (hb : ∀ g ∈ L, b g ∈ L) (hab : Commute a b) :
    Commute ((a.restrictScalars ℤ).restrict ha) ((b.restrictScalars ℤ).restrict hb) := by
  ext x
  show a (b (x : Φ)) = b (a (x : Φ))
  simpa [Module.End.mul_apply] using DFunLike.congr_fun hab (x : Φ)

private lemma isTorsionFree_submodule {Φ : Type} [AddCommGroup Φ] [Module ℂ Φ]
    (L : Submodule ℤ Φ) : Module.IsTorsionFree ℤ ↥L := by
  constructor
  intro r hr x y hxy
  have hr0 : (r : ℤ) ≠ 0 := hr.left.ne_zero
  apply Subtype.ext
  have hΦ : r • (x : Φ) = r • (y : Φ) := by
    have := congrArg (Subtype.val) hxy
    simpa using this
  have hc : ((r : ℂ)) • (x : Φ) = ((r : ℂ)) • (y : Φ) := by
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact hΦ
  exact smul_right_injective Φ (by exact_mod_cast hr0 : (r : ℂ) ≠ 0) hc

private lemma exists_int_congr_of_adjoin {T : Type} [CommRing T] {G : Set T} {𝔐 : Ideal T}
    (hG : ∀ g ∈ G, ∃ c : ℤ, g - (c : T) ∈ 𝔐) {t : T} (ht : t ∈ Algebra.adjoin ℤ G) :
    ∃ c : ℤ, t - (c : T) ∈ 𝔐 := by
  induction ht using Algebra.adjoin_induction with
  | mem g hg => exact hG g hg
  | algebraMap r =>
      refine ⟨r, ?_⟩
      have : (algebraMap ℤ T) r = ((r : ℤ) : T) := by
        simp [algebraMap_int_eq]
      rw [this, sub_self]
      exact 𝔐.zero_mem
  | add x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      refine ⟨c + d, ?_⟩
      have hid : x + y - ((c + d : ℤ) : T) = (x - (c : T)) + (y - (d : T)) := by
        push_cast
        ring
      rw [hid]
      exact 𝔐.add_mem hc hd
  | mul x y hx hy ihx ihy =>
      obtain ⟨c, hc⟩ := ihx
      obtain ⟨d, hd⟩ := ihy
      refine ⟨c * d, ?_⟩
      have hid : x * y - ((c * d : ℤ) : T) =
          x * (y - (d : T)) + (d : T) * (x - (c : T)) := by
        push_cast
        ring
      rw [hid]
      exact 𝔐.add_mem (𝔐.mul_mem_left _ hd) (𝔐.mul_mem_left _ hc)

private lemma residualCharacter.congr_aux {T : Type} [CommRing T] {k : Type} [CommRing k]
    (𝔐 : Ideal T) (ψ : ℤ →+* k)
    (hall : ∀ t : T, ∃ c : ℤ, t - (c : T) ∈ 𝔐)
    (hker : ∀ m : ℤ, ((m : ℤ) : T) ∈ 𝔐 → ψ m = 0)
    (t : T) (c : ℤ) (hc : t - (c : T) ∈ 𝔐) : ψ (hall t).choose = ψ c := by
  have hch := (hall t).choose_spec
  have hmem : (((hall t).choose - c : ℤ) : T) ∈ 𝔐 := by
    have hid : (((hall t).choose - c : ℤ) : T) =
        (t - (c : T)) - (t - ((hall t).choose : T)) := by
      push_cast
      ring
    rw [hid]
    exact 𝔐.sub_mem hc hch
  have h0 := hker _ hmem
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

private theorem nonpos_coe_eq_zero {M : ℕ} [NeZero M] {w : ℤ} (hw : w ≤ 0)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) w) : ⇑F = 0 := by
  let Fm : ModularForm (CongruenceSubgroup.Gamma0 M) w :=
    { toSlashInvariantForm := F.toSlashInvariantForm
      holo' := F.holo'
      bdd_at_cusps' := fun hc g hg =>
        Filter.ZeroAtFilter.boundedAtFilter (F.zero_at_cusps' hc g hg) }
  rcases hw.lt_or_eq with hlt | heq
  · have h0 := ModularForm.isZero_of_neg_weight hlt Fm
    have hFm : ⇑F = ⇑Fm := rfl
    rw [hFm, h0]
    rfl
  · subst heq
    obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero Fm
    have hinf : IsCusp OnePoint.infty
        (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 M)) :=
      Subgroup.isCusp_of_mem_strictPeriods one_pos
        (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 M)
    have hz : UpperHalfPlane.IsZeroAtImInfty
        (SlashAction.map (0 : ℤ) (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ) ⇑F) :=
      F.zero_at_cusps' hinf 1 (by simp)
    rw [SlashAction.slash_one] at hz
    have hFm : ⇑F = ⇑Fm := rfl
    rw [hFm, hc] at hz ⊢
    have hz' : Filter.Tendsto (Function.const UpperHalfPlane c)
        UpperHalfPlane.atImInfty (nhds 0) := hz
    have hc0 : c = 0 := (tendsto_nhds_unique hz' tendsto_const_nhds).symm
    rw [hc0]
    rfl

private def congrIdeal {A V : Type} [CommRing A] [AddCommGroup V] [Module A V]
    (P : V → Prop) (hP0 : P 0) (hPadd : ∀ {x y : V}, P x → P y → P (x + y))
    (hPsmul : ∀ (a : A) {x : V}, P x → P (a • x)) (v₀ : V) : Ideal A where
  carrier := {a | P (a • v₀)}
  zero_mem' := by simpa using hP0
  add_mem' := fun {a b} ha hb => by simpa [add_smul] using hPadd ha hb
  smul_mem' := fun c {t} ht => by simpa [smul_eq_mul, mul_smul] using hPsmul c ht

private lemma mem_congrIdeal {A V : Type} [CommRing A] [AddCommGroup V] [Module A V]
    {P : V → Prop} {hP0 : P 0} {hPadd : ∀ {x y : V}, P x → P y → P (x + y)}
    {hPsmul : ∀ (a : A) {x : V}, P x → P (a • x)} {v₀ : V} {a : A} :
    a ∈ congrIdeal P hP0 hPadd hPsmul v₀ ↔ P (a • v₀) := Iff.rfl

section IntegralLattice
open UpperHalfPlane
open scoped MatrixGroups ModularForm NumberField

namespace LatticeAux

private lemma one_mem (N : ℕ) : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

private lemma qCoeff_add {N : ℕ} {k : ℤ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  change PowerSeries.coeff n (qExpansion 1 ⇑(f + g)) =
    PowerSeries.coeff n (qExpansion 1 ⇑f) + PowerSeries.coeff n (qExpansion 1 ⇑g)
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem N) f g, map_add]

private lemma qCoeff_smul {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (e : ℂ) (n : ℕ) :
    qCoeff (⇑(e • f)) n = e * qCoeff (⇑f) n := by
  change PowerSeries.coeff n (qExpansion 1 ⇑(e • f)) = e * PowerSeries.coeff n (qExpansion 1 ⇑f)
  rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem N) e f, PowerSeries.coeff_smul,
    smul_eq_mul]

private lemma qCoeff_zero' {N : ℕ} {k : ℤ} (n : ℕ) : qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) k)) n = 0 := by
  have := qCoeff_smul (0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) 0 n
  rw [zero_smul, zero_mul] at this
  exact this

private lemma qCoeff_neg {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff (⇑(-f)) n = - qCoeff (⇑f) n := by
  have := qCoeff_smul f (-1) n
  rw [neg_one_smul] at this
  rw [this]; ring

private lemma eq_zero_of_qCoeff_eq_zero {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : ∀ n, qCoeff (⇑f) n = 0) : f = 0 := by
  apply DFunLike.coe_injective
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem N)⟩
  funext τ
  have hsum := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem N)) (holo f)
    (bdd_at_infty f) τ
  have hzero : (fun m : ℕ => PowerSeries.coeff m (qExpansion 1 ⇑f) • Function.Periodic.qParam 1 (τ : ℂ) ^ m) =
      fun _ => 0 := by
    funext m
    rw [show PowerSeries.coeff m (qExpansion 1 ⇑f) = qCoeff (⇑f) m from rfl, hf m, zero_smul]
  rw [hzero] at hsum
  change f τ = (0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) τ
  rw [CuspForm.zero_apply]
  exact hsum.unique hasSum_zero

private lemma qCoeff_heckeTLin {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    qCoeff (⇑(heckeTLin k hℓ hℓN f)) n =
      qCoeff (⇑f) (n * ℓ) + (if ℓ ∣ n then (ℓ : ℂ) ^ (k - 1) * qCoeff (⇑f) (n / ℓ) else 0) := by
  rw [CuspForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT f (one_mem N) hℓ.ne_zero n,
    ModularForm.coeffHeckeT_apply]

private lemma qCoeff_heckeULin {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {q : ℕ}
    (hq : q ≠ 0) (hqN : q ∣ N) (n : ℕ) : qCoeff (⇑(heckeULin k hqN f)) n = qCoeff (⇑f) (n * q) := by
  rw [CuspForm.coe_heckeULin_apply, ModularFormClass.qCoeff_heckeU f (one_mem N) hq n, ModularForm.coeffHeckeU_apply]

private lemma exists_finset_sep_of_sep {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (φ : ℕ → (V →ₗ[ℂ] ℂ))
    (hsep : ∀ v : V, (∀ n : ℕ, φ n v = 0) → v = 0) :
    ∃ A : Finset ℕ, ∀ v : V, (∀ n ∈ A, φ n v = 0) → v = 0 := by
  classical
  set K : Finset ℕ → Submodule ℂ V := fun A => ⨅ n ∈ A, LinearMap.ker (φ n) with hKdef
  set D : Set ℕ := Set.range fun A => Module.finrank ℂ (K A) with hDdef
  have hDne : D.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Finset ℕ, Module.finrank ℂ (K A₀) = sInf D := Nat.sInf_mem hDne
  refine ⟨A₀, fun v hv => ?_⟩
  have hvK : v ∈ K A₀ := by
    rw [hKdef]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    exact fun n hn => hv n hn
  by_contra hv0
  obtain ⟨m, hm⟩ : ∃ m : ℕ, φ m v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv0 (hsep v hall)
  have hlt : K (insert m A₀) < K A₀ := by
    refine lt_of_le_of_ne ?_ ?_
    · rw [hKdef]
      exact le_iInf₂ fun n hn => iInf₂_le n (Finset.mem_insert_of_mem hn)
    · intro heq
      have hvK' : v ∈ K (insert m A₀) := heq ▸ hvK
      rw [hKdef] at hvK'
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hvK'
      exact hm (hvK' m (Finset.mem_insert_self m A₀))
  have hrk : Module.finrank ℂ (K (insert m A₀)) < Module.finrank ℂ (K A₀) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hmem : Module.finrank ℂ (K (insert m A₀)) ∈ D := ⟨insert m A₀, rfl⟩
  have := Nat.sInf_le hmem
  omega

end LatticeAux

open LatticeAux in

private theorem exists_coeffLattice (M : ℕ) [NeZero M] (w : ℤ) (hw : 1 ≤ w)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    ∃ L : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 M) w),
      (∀ g, g ∈ L ↔ ∀ n : ℕ, (∃ x : integralClosure ℤ ℂ, (x : ℂ) = qCoeff g n) ∧ qCoeff g n ∈ K) ∧
      Module.Finite ℤ L ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ g ∈ L, heckeTLin w hℓ hℓM g ∈ L) ∧
      (∀ (q : ℕ) (hqM : q ∣ M), ∀ g ∈ L, heckeULin w hqM g ∈ L) := by
  classical
  have hM0 : M ≠ 0 := NeZero.ne M

  let P : CuspForm (CongruenceSubgroup.Gamma0 M) w → Prop := fun g =>
    ∀ n : ℕ, (∃ x : integralClosure ℤ ℂ, (x : ℂ) = qCoeff g n) ∧ qCoeff g n ∈ K
  have hP0 : P 0 := fun n =>
    ⟨⟨0, by rw [qCoeff_zero']; simp⟩, by rw [qCoeff_zero']; exact K.zero_mem⟩
  have hPadd : ∀ f g, P f → P g → P (f + g) := by
    intro f g hf hg n
    obtain ⟨x, hx⟩ := (hf n).1
    obtain ⟨y, hy⟩ := (hg n).1
    refine ⟨⟨x + y, by rw [AddMemClass.coe_add, qCoeff_add, hx, hy]⟩, ?_⟩
    rw [qCoeff_add]; exact K.add_mem (hf n).2 (hg n).2
  have hPneg : ∀ f, P f → P (-f) := by
    intro f hf n
    obtain ⟨x, hx⟩ := (hf n).1
    refine ⟨⟨-x, by rw [NegMemClass.coe_neg, qCoeff_neg, hx]⟩, ?_⟩
    rw [qCoeff_neg]; exact K.neg_mem (hf n).2
  let L₀ : AddSubgroup (CuspForm (CongruenceSubgroup.Gamma0 M) w) :=
    { carrier := {g | P g}
      add_mem' := fun {f g} hf hg => hPadd f g hf hg
      zero_mem' := hP0
      neg_mem' := fun {f} hf => hPneg f hf }
  let L : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 M) w) := AddSubgroup.toIntSubmodule L₀
  have hLmem : ∀ g, g ∈ L ↔ P g := fun g => Iff.rfl
  refine ⟨L, hLmem, ?_, ?_, ?_⟩
  ·
    haveI := CuspForm.finiteDimensional_cuspForm M w
    haveI : NumberField K :=
      { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
        to_finiteDimensional := inferInstance }
    let φ : ℕ → (CuspForm (CongruenceSubgroup.Gamma0 M) w →ₗ[ℂ] ℂ) := fun n =>
      { toFun := fun g => qCoeff g n
        map_add' := fun f g => qCoeff_add f g n
        map_smul' := fun c f => qCoeff_smul f c n }
    obtain ⟨A, hA⟩ := exists_finset_sep_of_sep φ (fun g hg => eq_zero_of_qCoeff_eq_zero g hg)

    have hint : ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 M) w) (hg : P g) (n : ℕ),
        (⟨qCoeff g n, (hg n).2⟩ : K) ∈ integralClosure ℤ K := by
      intro g hg n
      obtain ⟨x, hx⟩ := (hg n).1
      rw [mem_integralClosure_iff]
      refine (isIntegral_algHom_iff ((algebraMap K ℂ).toIntAlgHom) (algebraMap K ℂ).injective).mp ?_
      rw [RingHom.toIntAlgHom_apply, show algebraMap K ℂ ⟨qCoeff g n, (hg n).2⟩ = qCoeff g n from rfl, ← hx]
      exact x.2
    haveI : IsNoetherian ℤ (integralClosure ℤ K) := inferInstanceAs (IsNoetherian ℤ (𝓞 K))
    let ψ : L →+ (↥A → integralClosure ℤ K) :=
      { toFun := fun g n =>
          ⟨⟨qCoeff (g : CuspForm (CongruenceSubgroup.Gamma0 M) w) (n : ℕ), (g.2 (n : ℕ)).2⟩, hint _ g.2 (n : ℕ)⟩
        map_zero' := by
          funext n
          apply Subtype.ext
          apply Subtype.ext
          exact qCoeff_zero' (n : ℕ)
        map_add' := by
          intro f g
          funext n
          apply Subtype.ext
          apply Subtype.ext
          exact qCoeff_add (f : CuspForm (CongruenceSubgroup.Gamma0 M) w) g (n : ℕ) }
    have hψapply : ∀ (g : L) (n : ↥A),
        (((ψ g n : integralClosure ℤ K) : K) : ℂ) = qCoeff (⇑(g : CuspForm (CongruenceSubgroup.Gamma0 M) w)) n :=
      fun _ _ => rfl
    have hψ : Function.Injective ψ := by
      intro f g hfg
      apply Subtype.ext
      have hsub : ψ (f - g) = 0 := by rw [map_sub, hfg, sub_self]
      have hzero : ((f - g : L) : CuspForm (CongruenceSubgroup.Gamma0 M) w) = 0 := by
        apply hA
        intro n hn
        have h1 := congrFun hsub ⟨n, hn⟩
        have h2 := hψapply (f - g) ⟨n, hn⟩
        rw [h1] at h2
        exact h2.symm
      rw [Submodule.coe_sub, sub_eq_zero] at hzero
      exact hzero
    exact Module.Finite.of_injective ψ.toIntLinearMap hψ
  ·
    intro ℓ hℓ hℓM g hg
    rw [hLmem] at hg ⊢
    intro n
    have hpow : (ℓ : ℂ) ^ (w - 1) = (((ℓ ^ (w - 1).toNat : ℕ)) : ℂ) := by
      rw [Nat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    rw [qCoeff_heckeTLin g hℓ hℓM n, hpow]
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := (hg (n * ℓ)).1
      obtain ⟨y, hy⟩ := (hg (n / ℓ)).1
      by_cases hℓn : ℓ ∣ n
      · refine ⟨x + (ℓ ^ (w - 1).toNat : ℕ) * y, ?_⟩
        rw [if_pos hℓn]; push_cast; rw [hx, hy]
      · refine ⟨x, ?_⟩
        rw [if_neg hℓn, add_zero, hx]
    · by_cases hℓn : ℓ ∣ n
      · rw [if_pos hℓn]
        exact K.add_mem (hg _).2 (K.mul_mem (by exact_mod_cast K.natCast_mem _) (hg _).2)
      · rw [if_neg hℓn, add_zero]; exact (hg _).2
  ·
    intro q hqM g hg
    rw [hLmem] at hg ⊢
    intro n
    have hq0 : q ≠ 0 := fun h => hM0 (Nat.eq_zero_of_zero_dvd (h ▸ hqM))
    rw [qCoeff_heckeULin g hq0 hqM n]
    exact hg _

end IntegralLattice

section LocalUnitRescale
open scoped NumberField

private theorem exists_rescale_local_unit (E : IntermediateField ℚ ℂ) [FiniteDimensional ℚ E]
    (𝔪' : Ideal (integralClosure ℤ ℂ)) (h𝔪' : 𝔪'.IsPrime) {p : ℕ} (hp : p.Prime)
    (hp𝔪' : (p : integralClosure ℤ ℂ) ∈ 𝔪')
    (a : ℕ → ℂ) (haE : ∀ n, a n ∈ E) (haint : ∀ n, ∃ x : integralClosure ℤ ℂ, (x : ℂ) = a n)
    (hne : ∃ n, a n ≠ 0) :
    ∃ c : ℂ, (∀ n, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧ (x : ℂ) = y * (c * a n)) ∧
      (∃ (n : ℕ) (x y : integralClosure ℤ ℂ), y ∉ 𝔪' ∧ (x : ℂ) = y * (c * a n) ∧ x ∉ 𝔪') := by
  classical
  haveI := h𝔪'
  haveI : NumberField E :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ E).injective
      to_finiteDimensional := inferInstance }

  let φ : 𝓞 E →+* integralClosure ℤ ℂ :=
    ((algebraMap E ℂ).comp (algebraMap (𝓞 E) E)).codRestrict (integralClosure ℤ ℂ)
      (fun z => map_isIntegral_int (algebraMap E ℂ) (NumberField.RingOfIntegers.isIntegral_coe z))
  have hφ : ∀ z : 𝓞 E, (φ z : ℂ) = ((algebraMap (𝓞 E) E z : E) : ℂ) := fun _ => rfl
  let 𝔮 : Ideal (𝓞 E) := 𝔪'.comap φ
  haveI h𝔮 : 𝔮.IsPrime := Ideal.IsPrime.comap φ
  have h𝔮ne : 𝔮 ≠ ⊥ := by
    intro h
    have hpq : ((p : ℕ) : 𝓞 E) ∈ 𝔮 := by
      change φ (p : 𝓞 E) ∈ 𝔪'
      rw [map_natCast]; exact hp𝔪'
    rw [h, Ideal.mem_bot] at hpq
    exact hp.ne_zero (by exact_mod_cast hpq)

  let S := Localization.AtPrime 𝔮
  haveI : IsDiscreteValuationRing S :=
    @IsDedekindDomainDvr.is_dvr_at_nonzero_prime (𝓞 E) _ inferInstance inferInstance 𝔮 h𝔮ne h𝔮
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  let g : 𝓞 E →+* E := algebraMap (𝓞 E) E
  have hg : ∀ y : 𝔮.primeCompl, IsUnit (g y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ?_)
    intro hy; exact y.2 (hy ▸ 𝔮.zero_mem)
  let ι : S →+* E := IsLocalization.lift (M := 𝔮.primeCompl) hg
  have hι_alg : ∀ z : 𝓞 E, ι (algebraMap (𝓞 E) S z) = g z := fun z => IsLocalization.lift_eq hg z
  have hι_mk' : ∀ (x : 𝓞 E) (y : 𝔮.primeCompl), g x = g y * ι (IsLocalization.mk' S x y) :=
    fun x y => (IsLocalization.lift_mk'_spec (M := 𝔮.primeCompl) hg x (ι (IsLocalization.mk' S x y)) y).mp rfl
  have hι0 : ∀ z : S, ι z = 0 → z = 0 := by
    intro z hz
    obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq 𝔮.primeCompl z
    have := hι_mk' x y
    rw [hz, mul_zero, NumberField.RingOfIntegers.coe_eq_zero_iff] at this
    rw [this, IsLocalization.mk'_zero]
  have hιϖ : ι ϖ ≠ 0 := fun h => hϖ.ne_zero (hι0 ϖ h)

  have hβint : ∀ n, IsIntegral ℤ (⟨a n, haE n⟩ : E) := by
    intro n
    obtain ⟨x, hx⟩ := haint n
    refine (isIntegral_algHom_iff ((algebraMap E ℂ).toIntAlgHom) (algebraMap E ℂ).injective).mp ?_
    rw [RingHom.toIntAlgHom_apply, show algebraMap E ℂ ⟨a n, haE n⟩ = a n from rfl, ← hx]
    exact x.2
  let β : ℕ → 𝓞 E := fun n => ⟨⟨a n, haE n⟩, hβint n⟩
  have hβ : ∀ n, ((g (β n) : E) : ℂ) = a n := fun _ => rfl
  let b : ℕ → S := fun n => algebraMap (𝓞 E) S (β n)
  have hb0 : ∀ n, b n = 0 ↔ a n = 0 := by
    intro n
    constructor
    · intro h
      have : β n = 0 := (IsLocalization.injective S 𝔮.primeCompl_le_nonZeroDivisors) (by rw [map_zero]; exact h)
      have := congrArg (fun z : 𝓞 E => ((g z : E) : ℂ)) this
      simpa [hβ] using this
    · intro h
      have : β n = 0 := by
        apply NumberField.RingOfIntegers.ext
        apply Subtype.ext
        exact h
      simp only [b, this, map_zero]

  have hdec : ∀ n, ∃ (k : ℕ) (u : Sˣ), b n ≠ 0 → b n = u * ϖ ^ k := by
    intro n
    by_cases h : b n = 0
    · exact ⟨0, 1, fun h' => (h' h).elim⟩
    · obtain ⟨k, u, hku⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h hϖ
      exact ⟨k, u, fun _ => hku⟩
  choose k u hku using hdec
  obtain ⟨n₁, hn₁⟩ := hne
  have hex : ∃ m, ∃ n, b n ≠ 0 ∧ k n = m := ⟨k n₁, n₁, fun h => hn₁ ((hb0 n₁).mp h), rfl⟩
  let m := Nat.find hex
  obtain ⟨n₀, hn₀, hkn₀⟩ : ∃ n, b n ≠ 0 ∧ k n = m := Nat.find_spec hex
  have hmin : ∀ n, b n ≠ 0 → m ≤ k n := fun n hn => Nat.find_min' hex ⟨n, hn, rfl⟩

  let cE : E := (ι ϖ)⁻¹ ^ m
  have key : ∀ n, b n ≠ 0 → ∃ (x : 𝓞 E) (y : 𝔮.primeCompl),
      IsLocalization.mk' S x y = (u n : S) * ϖ ^ (k n - m) ∧ ((g x : E) : ℂ) = (g y : E) * (cE * a n) := by
    intro n hn
    obtain ⟨x, y, hxy⟩ := IsLocalization.exists_mk'_eq 𝔮.primeCompl ((u n : S) * ϖ ^ (k n - m))
    refine ⟨x, y, hxy, ?_⟩
    have h1 := hι_mk' x y
    rw [hxy] at h1
    have h2 : ι ((u n : S) * ϖ ^ (k n - m)) * (ι ϖ) ^ m = ι (b n) := by
      rw [hku n hn, map_mul, map_mul, map_pow, map_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel (hmin n hn)]
    have h3 : ι ((u n : S) * ϖ ^ (k n - m)) = cE * g (β n) := by
      rw [← hι_alg, ← h2]
      simp only [cE, inv_pow]
      field_simp
    rw [h1, h3]
    push_cast
    rw [hβ]
  refine ⟨(cE : ℂ), ?_, ?_⟩
  · intro n
    by_cases hn : b n = 0
    · refine ⟨0, 1, Ideal.one_notMem 𝔪', ?_⟩
      rw [(hb0 n).mp hn]; simp
    · obtain ⟨x, y, -, hxy⟩ := key n hn
      refine ⟨φ x, φ y, fun hy => y.2 (Ideal.mem_comap.mpr hy), ?_⟩
      rw [hφ, hφ, hxy]
  · obtain ⟨x, y, hxyu, hxy⟩ := key n₀ hn₀
    refine ⟨n₀, φ x, φ y, fun hy => y.2 (Ideal.mem_comap.mpr hy), by rw [hφ, hφ, hxy], ?_⟩
    have hunit : IsUnit (IsLocalization.mk' S x y) := by
      rw [hxyu, hkn₀, Nat.sub_self, pow_zero, mul_one]; exact Units.isUnit _
    have hx : x ∈ 𝔮.primeCompl := (IsLocalization.AtPrime.isUnit_mk'_iff S 𝔮 x y).mp hunit
    exact fun hx' => hx (Ideal.mem_comap.mpr hx')

end LocalUnitRescale

section CoefficientSums
open UpperHalfPlane
open scoped MatrixGroups ModularForm

open LatticeAux in

private theorem qCoeff_finset_sum {N : ℕ} {k : ℤ} {ι : Type} (s : Finset ι)
    (g : ι → CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff (⇑(∑ i ∈ s, g i)) n = ∑ i ∈ s, qCoeff (⇑(g i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact qCoeff_zero' n
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qCoeff_add, ih]

open LatticeAux in

private theorem qCoeff_smul_finset_sum_smul {N : ℕ} {k : ℤ} {ι : Type} (s : Finset ι)
    (g : ι → CuspForm (CongruenceSubgroup.Gamma0 N) k) (b : ι → ℂ) (a : ℂ) (n : ℕ) :
    qCoeff (⇑(a • ∑ i ∈ s, b i • g i)) n = ∑ i ∈ s, (a * b i) * qCoeff (⇑(g i)) n := by
  rw [qCoeff_smul, qCoeff_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qCoeff_smul, mul_assoc]

private theorem qCoeff_smul_finset_sum_smul' {N : ℕ} {k : ℤ} (F : IntermediateField ℚ ℂ)
    (s : Finset (CuspForm (CongruenceSubgroup.Gamma0 N) k)) (c : CuspForm (CongruenceSubgroup.Gamma0 N) k → F)
    (a : ℂ) (n : ℕ) :
    qCoeff (⇑(a • ∑ y ∈ s, c y • y)) n = ∑ y ∈ s, (a * (c y : ℂ)) * qCoeff (⇑y) n := by
  have h := qCoeff_smul_finset_sum_smul s id (fun y => (c y : ℂ)) a n
  simp only [id] at h
  rw [← h]
  rfl

private theorem exists_intermediateField_finiteDimensional_sum_mem (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (hc : ∀ i ∈ s, IsIntegral ℤ (c i))
    (b : ι → ℕ → ℂ) (hb : ∀ i ∈ s, ∀ n, b i n ∈ K) :
    ∃ E : IntermediateField ℚ ℂ, FiniteDimensional ℚ E ∧ ∀ n, ∑ i ∈ s, c i * b i n ∈ E := by
  classical
  let S : Set ℂ := ((s.image c : Finset ℂ) : Set ℂ)
  haveI : Finite S := (s.image c).finite_toSet.to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact (hc i hi).tower_top
  refine ⟨K ⊔ IntermediateField.adjoin ℚ S, inferInstance, fun n => ?_⟩
  refine sum_mem fun i hi => mul_mem ?_ ?_
  · exact (le_sup_right : IntermediateField.adjoin ℚ S ≤ K ⊔ IntermediateField.adjoin ℚ S)
      (IntermediateField.subset_adjoin ℚ S (Finset.mem_coe.mpr (Finset.mem_image_of_mem c hi)))
  · exact (le_sup_left : K ≤ K ⊔ IntermediateField.adjoin ℚ S) (hb i hi n)

end CoefficientSums

namespace DSOut

private noncomputable abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

private theorem exists_common_eigenvector_of_isAlgClosed
    {𝕜 : Type} [Field 𝕜] [IsAlgClosed 𝕜] {ι : Type} :
    ∀ (s : Finset ι) (V : Type) (_ : AddCommGroup V), ∀ (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : Nontrivial V) (f : ι → Module.End 𝕜 V),
      (∀ i ∈ s, ∀ j ∈ s, Commute (f i) (f j)) →
      ∃ v : V, v ≠ 0 ∧ ∀ i ∈ s, ∃ μ : 𝕜, f i v = μ • v := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
      intro V _ _ _ _ f _
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact ⟨v, hv, by simp⟩
  | insert a s ha ih =>
      intro V _ _ _ _ f hcomm
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f a)
      set E := Module.End.eigenspace (f a) μ with hEdef
      haveI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hμ
      have hstab : ∀ i ∈ s, ∀ x ∈ E, f i x ∈ E := by
        intro i hi x hx
        rw [hEdef, Module.End.mem_eigenspace_iff] at hx ⊢
        have hc : Commute (f a) (f i) :=
          hcomm a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        have hcx : f a (f i x) = f i (f a x) := by
          simpa [Module.End.mul_apply] using DFunLike.congr_fun hc x
        rw [hcx, hx, map_smul]
      let g : ι → Module.End 𝕜 E := fun i =>
        if hi : i ∈ s then (f i).restrict (hstab i hi) else 0
      have hgcomm : ∀ i ∈ s, ∀ j ∈ s, Commute (g i) (g j) := by
        intro i hi j hj
        have hc := hcomm i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
        ext x
        simp only [Module.End.mul_apply, g, dif_pos hi, dif_pos hj, LinearMap.restrict_apply]
        simpa [Module.End.mul_apply] using DFunLike.congr_fun hc (x : V)
      obtain ⟨v, hv0, hveig⟩ :=
        ih E inferInstance inferInstance inferInstance inferInstance g hgcomm
      refine ⟨(v : V), by simpa using hv0, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · exact ⟨μ, Module.End.mem_eigenspace_iff.mp v.2⟩
      · obtain ⟨ν, hν⟩ := hveig i his
        refine ⟨ν, ?_⟩
        have hco := congrArg Subtype.val hν
        simp only [g, dif_pos his] at hco
        rw [show ((f i).restrict (hstab i his) v : V) = f i (v : V) from rfl] at hco
        simpa using hco

open Polynomial in

private theorem isIntegral_of_eigenvalue_of_lattice {Φ : Type} [AddCommGroup Φ] [Module ℂ Φ]
    (L : Submodule ℤ Φ) [Module.Finite ℤ L] (t : Φ →ₗ[ℂ] Φ) (ht : ∀ g ∈ L, t g ∈ L)
    {v : Φ} (hv : v ∈ Submodule.span ℂ (L : Set Φ)) (hv0 : v ≠ 0) {μ : ℂ} (heig : t v = μ • v) :
    IsIntegral ℤ μ := by
  classical
  let tZ : Φ →ₗ[ℤ] Φ := t.toAddMonoidHom.toIntLinearMap
  have htZ : ∀ g ∈ L, tZ g ∈ L := ht
  let s : L →ₗ[ℤ] L := tZ.restrict htZ
  obtain ⟨P, hPmon, hPs⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℤ s
  have hpow : ∀ (k : ℕ) (x : L), (((s ^ k) x : L) : Φ) = (t ^ k) (x : Φ) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
        rfl
  have haeval : ∀ (Q : ℤ[X]) (x : L),
      ((aeval s Q x : L) : Φ) = aeval t (Q.map (algebraMap ℤ ℂ)) (x : Φ) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
        intro x; simp only [map_add, Polynomial.map_add, LinearMap.add_apply,
          Submodule.coe_add, hp, hq]
    | monomial n c =>
        intro x
        rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
          Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          Submodule.coe_smul, hpow, ← Int.cast_smul_eq_zsmul ℂ]
        rfl
  have hkill : ∀ x ∈ Submodule.span ℂ (L : Set Φ), aeval t (P.map (algebraMap ℤ ℂ)) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hxL =>
        have := haeval P ⟨x, hxL⟩
        rw [hPs, LinearMap.zero_apply, Submodule.coe_zero] at this
        exact this.symm
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hv' := hkill v hv
  rw [Module.End.aeval_apply_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr heig, hv0⟩,
    smul_eq_zero, eval_map] at hv'
  exact ⟨P, hPmon, hv'.resolve_right hv0⟩

private lemma extAgree {Φ : Type} [AddCommGroup Φ] [Module ℂ Φ] {L : Submodule ℤ Φ}
    (τ₁ τ₂ : Module.End ℂ Φ) (h : ∀ g ∈ L, τ₁ g = τ₂ g)
    {v : Φ} (hv : v ∈ Submodule.span ℂ (L : Set Φ)) : τ₁ v = τ₂ v := by
  induction hv using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, map_smul, ha]

open LatticeAux in
set_option maxHeartbeats 3200000 in

private theorem construct_output {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] (hpM : p ∣ M) {w : ℤ}
    (S : Set ℕ) (cT : ℕ → ℤ) (cU : ℤ)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (L : Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 M) w))
    (hLcoeff : ∀ g ∈ L, ∀ n : ℕ, (∃ z : integralClosure ℤ ℂ, (z : ℂ) = qCoeff g n) ∧
      qCoeff g n ∈ K)
    [hLfin : Module.Finite ℤ ↥L]
    {T : Type} [CommRing T] [Module T ↥L] [IsScalarTower ℤ T ↥L]
    [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
    (hTlin : ∀ t : T, ∃ τ : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) w),
      ∀ g : ↥L, ((t • g : ↥L) : CuspForm (CongruenceSubgroup.Gamma0 M) w) = τ ↑g)
    (opT : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M → T) (opU : T)
    (hopT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (g : ↥L),
      ((opT ℓ hℓ hℓS hℓM • g : ↥L) : CuspForm (CongruenceSubgroup.Gamma0 M) w) =
        heckeTLin w hℓ hℓM (g : CuspForm (CongruenceSubgroup.Gamma0 M) w))
    (hopU : ∀ (g : ↥L), ((opU • g : ↥L) : CuspForm (CongruenceSubgroup.Gamma0 M) w) =
      heckeULin w hpM (g : CuspForm (CongruenceSubgroup.Gamma0 M) w))
    {k : Type} [Field k] (χ : T →+* k) (hχp : χ p = 0)
    (hχT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
      χ (opT ℓ hℓ hℓS hℓM) = χ (cT ℓ))
    (hχU : χ opU = χ cU)
    (𝔭 : Ideal T) (h𝔭min : 𝔭 ∈ minimalPrimes T) (_h𝔭ker : 𝔭 ≤ RingHom.ker χ)
    (red : (T ⧸ 𝔭) →+* k) (hred : red.comp (Ideal.Quotient.mk 𝔭) = χ)
    (x : ↥L) (hxne : x ≠ 0) (h𝔭x : ∀ q ∈ 𝔭, q • x = 0)
    (_hann : ∀ r : T, r • x = 0 → r ∈ 𝔭) :
    ∃ 𝔪' : Ideal (integralClosure ℤ ℂ), 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 M) w,
      (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n) ∧
      (∃ (n : ℕ) (x y : integralClosure ℤ ℂ), y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n ∧ x ∉ 𝔪') ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
        ∃ lam : integralClosure ℤ ℂ, lam - cT ℓ ∈ 𝔪' ∧
          heckeTLin w hℓ hℓM f = (lam : ℂ) • f) ∧
      (∃ α : integralClosure ℤ ℂ, α - cU ∈ 𝔪' ∧ heckeULin w hpM f = (α : ℂ) • f) := by
  classical
  haveI h𝔭pr : 𝔭.IsPrime := h𝔭min.1.1
  haveI : Module.Finite ℤ (T ⧸ 𝔭) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔭).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral ℤ (T ⧸ 𝔭) := Algebra.IsIntegral.of_finite ℤ (T ⧸ 𝔭)
  let Φ := CuspForm (CongruenceSubgroup.Gamma0 M) w
  let τ : T → Module.End ℂ Φ := fun t => (hTlin t).choose
  have hτL : ∀ t (g : ↥L), τ t ↑g = ((t • g : ↥L) : Φ) :=
    fun t g => ((hTlin t).choose_spec g).symm
  have hτL_stab : ∀ t, ∀ g ∈ L, τ t g ∈ L := by
    intro t g hg; rw [hτL t ⟨g, hg⟩]; exact (t • (⟨g, hg⟩ : ↥L)).2
  let spL := Submodule.span ℂ (L : Set Φ)
  have hτ_add : ∀ a b, ∀ v ∈ spL, τ (a + b) v = τ a v + τ b v := fun a b v hv =>
    extAgree (τ (a + b)) (τ a + τ b) (fun g hg => by
      rw [LinearMap.add_apply, hτL (a + b) ⟨g, hg⟩, hτL a ⟨g, hg⟩, hτL b ⟨g, hg⟩,
        add_smul, Submodule.coe_add]) hv
  have hτ_mul : ∀ a b, ∀ v ∈ spL, τ (a * b) v = τ a (τ b v) := fun a b v hv =>
    extAgree (τ (a * b)) ((τ a).comp (τ b)) (fun g hg => by
      rw [LinearMap.comp_apply, hτL (a * b) ⟨g, hg⟩, hτL b ⟨g, hg⟩,
        hτL a (b • (⟨g, hg⟩ : ↥L)), mul_smul]) hv
  have hτ_one : ∀ v ∈ spL, τ 1 v = v := fun v hv =>
    extAgree (τ 1) LinearMap.id (fun g hg => by rw [hτL 1 ⟨g, hg⟩, one_smul]; rfl) hv
  have hτ_zero : ∀ v ∈ spL, τ 0 v = 0 := fun v hv =>
    extAgree (τ 0) 0 (fun g hg => by rw [hτL 0 ⟨g, hg⟩, zero_smul]; rfl) hv
  have hτ_zsmul : ∀ (n : ℤ) (t : T), ∀ v ∈ spL, τ (n • t) v = n • τ t v := fun n t v hv =>
    (extAgree (τ (n • t)) ((n : ℂ) • τ t) (fun g hg => by
      rw [LinearMap.smul_apply, hτL (n • t) ⟨g, hg⟩, hτL t ⟨g, hg⟩, smul_assoc,
        Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℂ]) hv).trans
      (by rw [LinearMap.smul_apply, Int.cast_smul_eq_zsmul])
  haveI hQbar_alg : IsAlgClosed ↥Qbar :=
    (algebraicClosure.isAlgClosure (F := ℚ) (E := ℂ)).isAlgClosed

  obtain ⟨GT, hGT⟩ := (inferInstance : Module.Finite ℤ T).fg_top
  let orbitGen : Finset Φ := GT.image (fun g => ((g • x : ↥L) : Φ))
  let VQbar := Submodule.span ↥Qbar (orbitGen : Set Φ)
  have horbit_VQbar : ∀ t : T, ((t • x : ↥L) : Φ) ∈ VQbar := by
    intro t
    have htG : t ∈ Submodule.span ℤ (GT : Set T) := hGT ▸ Submodule.mem_top
    induction htG using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hg))
    | zero => simp [VQbar]
    | add a b _ _ ha hb =>
        rw [add_smul, Submodule.coe_add]; exact Submodule.add_mem _ ha hb
    | smul n a _ ha =>
        rw [smul_assoc, Submodule.coe_smul_of_tower,
          ← Int.cast_smul_eq_zsmul ↥Qbar n ((a • x : ↥L) : Φ)]
        exact Submodule.smul_mem _ _ ha
  have hVQbar_spL : ∀ v ∈ VQbar, v ∈ spL := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        exact Submodule.subset_span (g • x).2
    | zero => simp [spL]
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c a _ ha => exact Submodule.smul_mem _ (c : ℂ) ha
  haveI hVQbar_fd : FiniteDimensional ↥Qbar ↥VQbar :=
    FiniteDimensional.span_of_finite ↥Qbar orbitGen.finite_toSet
  have hτ_VQbar_stab : ∀ (t : T), ∀ v ∈ VQbar, τ t v ∈ VQbar := by
    intro t v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        rw [hτL, ← mul_smul]; exact horbit_VQbar (t * g)
    | zero => simp [VQbar]
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
        rw [show τ t (c • a) = c • τ t a from (τ t).map_smul (c : ℂ) a]
        exact Submodule.smul_mem _ c ha
  let τV : T → Module.End ↥Qbar ↥VQbar := fun t =>
    { toFun := fun v => ⟨τ t ↑v, hτ_VQbar_stab t ↑v v.2⟩
      map_add' := fun v₁ v₂ => Subtype.ext (by simp [Submodule.coe_add, map_add])
      map_smul' := fun c v => Subtype.ext ((τ t).map_smul (c : ℂ) ↑v) }
  have hτV_coe : ∀ t (v : ↥VQbar), ((τV t v : ↥VQbar) : Φ) = τ t ↑v := fun _ _ => rfl
  have hτV_comm : ∀ t₁ t₂, Commute (τV t₁) (τV t₂) := by
    intro t₁ t₂
    refine LinearMap.ext fun v => Subtype.ext ?_
    show τ t₁ (τ t₂ ↑v) = τ t₂ (τ t₁ ↑v)
    rw [← hτ_mul t₁ t₂ _ (hVQbar_spL _ v.2), ← hτ_mul t₂ t₁ _ (hVQbar_spL _ v.2), mul_comm]
  have hx_VQbar : ((x : ↥L) : Φ) ∈ VQbar := by have := horbit_VQbar 1; rwa [one_smul] at this
  haveI hVQbar_nt : Nontrivial ↥VQbar := by
    refine ⟨⟨⟨_, hx_VQbar⟩, 0, ?_⟩⟩
    simpa using fun h => hxne (Subtype.ext h)
  obtain ⟨f₀, hf₀ne, hf₀eig⟩ :=
    exists_common_eigenvector_of_isAlgClosed (𝕜 := ↥Qbar) GT ↥VQbar inferInstance inferInstance
      inferInstance inferInstance τV (fun i _ j _ => hτV_comm i j)
  have hf₀sp : (f₀ : Φ) ∈ spL := hVQbar_spL _ f₀.2
  have hf₀ne' : (f₀ : Φ) ≠ 0 := by simpa using hf₀ne
  have hf₀eigT : ∀ t : T, ∃ μ : ℂ, τ t (f₀ : Φ) = μ • (f₀ : Φ) := by
    intro t
    have htG : t ∈ Submodule.span ℤ (GT : Set T) := hGT ▸ Submodule.mem_top
    induction htG using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨μ, hμ⟩ := hf₀eig g hg
        exact ⟨(μ : ℂ), congrArg (Subtype.val : ↥VQbar → Φ) hμ⟩
    | zero => exact ⟨0, by rw [hτ_zero _ hf₀sp, zero_smul]⟩
    | add a b _ _ ha hb =>
        obtain ⟨μa, hμa⟩ := ha; obtain ⟨μb, hμb⟩ := hb
        exact ⟨μa + μb, by rw [hτ_add _ _ _ hf₀sp, hμa, hμb, add_smul]⟩
    | smul n a _ ha =>
        obtain ⟨μ, hμ⟩ := ha
        exact ⟨n * μ, by
          rw [hτ_zsmul n a _ hf₀sp, hμ, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]⟩
  let evℂ : T → ℂ := fun t => (hf₀eigT t).choose
  have hevℂ : ∀ t, τ t (f₀ : Φ) = evℂ t • (f₀ : Φ) := fun t => (hf₀eigT t).choose_spec
  have hevℂ_unique : ∀ t μ, τ t (f₀ : Φ) = μ • (f₀ : Φ) → evℂ t = μ := by
    intro t μ hμ
    have := (hevℂ t).symm.trans hμ
    rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero, or_iff_left hf₀ne', sub_eq_zero] at this
  have hevℂ_int : ∀ t, IsIntegral ℤ (evℂ t) := fun t =>
    isIntegral_of_eigenvalue_of_lattice L (τ t) (hτL_stab t) hf₀sp hf₀ne' (hevℂ t)
  let ev : T →+* integralClosure ℤ ℂ :=
    { toFun := fun t => ⟨evℂ t, hevℂ_int t⟩
      map_one' := Subtype.ext (hevℂ_unique 1 1 (by rw [hτ_one _ hf₀sp, one_smul]))
      map_mul' := fun a b => Subtype.ext (hevℂ_unique (a * b) (evℂ a * evℂ b) (by
        rw [hτ_mul _ _ _ hf₀sp, hevℂ b, (τ a).map_smul, hevℂ a, smul_smul, mul_comm]))
      map_zero' := Subtype.ext (hevℂ_unique 0 0 (by rw [hτ_zero _ hf₀sp, zero_smul]))
      map_add' := fun a b => Subtype.ext (hevℂ_unique (a + b) (evℂ a + evℂ b) (by
        rw [hτ_add _ _ _ hf₀sp, hevℂ, hevℂ, add_smul])) }
  have hev_coe : ∀ t, ((ev t : integralClosure ℤ ℂ) : ℂ) = evℂ t := fun _ => rfl
  have h𝔭kev : ∀ q ∈ 𝔭, ev q = 0 := by
    intro q hq
    refine Subtype.ext (hevℂ_unique q 0 ?_)
    rw [zero_smul]
    have hτq_VQbar : ∀ v ∈ VQbar, τ q v = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
          rw [hτL, show q • (g • x) = (0 : ↥L) from by
            rw [smul_comm, h𝔭x q hq, smul_zero], Submodule.coe_zero]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | smul c a _ ha =>
          rw [show (c • a : Φ) = (c : ℂ) • a from rfl, (τ q).map_smul, ha, smul_zero]
    exact hτq_VQbar ↑f₀ f₀.2
  let evQ : (T ⧸ 𝔭) →+* integralClosure ℤ ℂ := Ideal.Quotient.lift 𝔭 ev h𝔭kev
  have hevQ_inj : Function.Injective evQ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hz0

    have hz_int : IsIntegral ℤ z := Algebra.IsIntegral.isIntegral z
    have hset_ne : {n : ℕ | ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = n ∧
        Polynomial.aeval z P = 0}.Nonempty := ⟨_, hz_int.choose, hz_int.choose_spec.1, rfl,
          hz_int.choose_spec.2⟩
    obtain ⟨P, hPmon, hPdeg, hPz⟩ := Nat.find_spec hset_ne

    have hn₀1 : 1 ≤ Nat.find hset_ne := by
      rcases Nat.eq_zero_or_pos (Nat.find hset_ne) with h0 | h1
      · exfalso
        rw [Polynomial.eq_one_of_monic_natDegree_zero hPmon (hPdeg.trans h0), map_one] at hPz
        exact one_ne_zero hPz
      · exact h1

    have ha₀ne : P.coeff 0 ≠ 0 := by
      intro ha₀
      have hPfact : P = Polynomial.X * P.divX := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add P, ha₀, map_zero, add_zero]
      have hdivX_mon : P.divX.Monic := by
        have hm := hPmon
        rw [hPfact, Polynomial.Monic.def, Polynomial.leadingCoeff_mul,
          Polynomial.leadingCoeff_X, one_mul] at hm
        exact hm
      have hdivX_z : Polynomial.aeval z P.divX = 0 := by
        have hh := hPz; rw [hPfact, map_mul, Polynomial.aeval_X] at hh
        exact (mul_eq_zero.mp hh).resolve_left hz0
      have hne : P.divX ≠ 0 := hdivX_mon.ne_zero
      have heq : P.natDegree = 1 + P.divX.natDegree := by
        conv_lhs => rw [hPfact]
        rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hne, Polynomial.natDegree_X]
      have hle : Nat.find hset_ne ≤ P.divX.natDegree :=
        Nat.find_min' hset_ne ⟨P.divX, hdivX_mon, rfl, hdivX_z⟩
      omega

    have hfact : (algebraMap ℤ (T ⧸ 𝔭) (P.coeff 0)) = -(z * Polynomial.aeval z P.divX) := by
      have h1 : z * Polynomial.aeval z P.divX + algebraMap ℤ (T ⧸ 𝔭) (P.coeff 0) = 0 := by
        have := hPz
        conv_lhs at this => rw [← Polynomial.X_mul_divX_add P]
        rwa [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at this
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
    have ha₀ker : (P.coeff 0 : integralClosure ℤ ℂ) = 0 := by
      have := congrArg evQ hfact
      rw [map_neg, map_mul, hz, zero_mul, neg_zero,
        show algebraMap ℤ (T ⧸ 𝔭) (P.coeff 0) = ((P.coeff 0 : ℤ) : T ⧸ 𝔭) from rfl,
        map_intCast] at this
      exact this
    exact ha₀ne (by exact_mod_cast ha₀ker)
  letI algQ : Algebra (T ⧸ 𝔭) (integralClosure ℤ ℂ) := evQ.toAlgebra
  haveI halgQint : Algebra.IsIntegral (T ⧸ 𝔭) (integralClosure ℤ ℂ) := by
    constructor; intro z
    have hz : IsIntegral ℤ z := Algebra.IsIntegral.isIntegral z
    obtain ⟨P, hPmon, hPz⟩ := hz
    refine ⟨P.map (algebraMap ℤ (T ⧸ 𝔭)), hPmon.map _, ?_⟩
    have hcomp : (algebraMap (T ⧸ 𝔭) (integralClosure ℤ ℂ)).comp (algebraMap ℤ (T ⧸ 𝔭)) =
        algebraMap ℤ (integralClosure ℤ ℂ) := RingHom.ext_int _ _
    rw [Polynomial.eval₂_map, hcomp]
    exact hPz
  let 𝔮 : Ideal (T ⧸ 𝔭) := RingHom.ker red
  haveI h𝔮pr : 𝔮.IsPrime := RingHom.ker_isPrime red
  have hp𝔮 : ((p : ℕ) : T ⧸ 𝔭) ∈ 𝔮 := by
    show red p = 0
    rw [show ((p : ℕ) : T ⧸ 𝔭) = Ideal.Quotient.mk 𝔭 (p : T) from (map_natCast _ p).symm,
      ← RingHom.comp_apply, hred, hχp]
  have hcomap_bot : Ideal.comap (algebraMap (T ⧸ 𝔭) (integralClosure ℤ ℂ)) ⊥ ≤ 𝔮 := by
    have halg : (algebraMap (T ⧸ 𝔭) (integralClosure ℤ ℂ)) = evQ := rfl
    rw [halg, Ideal.comap_bot_of_injective _ hevQ_inj]; exact bot_le
  obtain ⟨𝔪', -, h𝔪'pr, h𝔪'over⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral 𝔮 (⊥ : Ideal (integralClosure ℤ ℂ)) hcomap_bot
  haveI : 𝔪'.IsPrime := h𝔪'pr
  have hevQ_comap : Ideal.comap evQ 𝔪' = 𝔮 := h𝔪'over
  have hp𝔪' : (p : integralClosure ℤ ℂ) ∈ 𝔪' := by
    have hmem : ((p : ℕ) : T ⧸ 𝔭) ∈ Ideal.comap evQ 𝔪' := hevQ_comap ▸ hp𝔮
    simpa [Ideal.mem_comap, map_natCast] using hmem
  have h𝔪'max : 𝔪'.IsMaximal := by
    haveI : Algebra.IsIntegral ℤ (integralClosure ℤ ℂ) := integralClosure.AlgebraIsIntegral
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ) 𝔪' ?_
    haveI hcomapPr : (𝔪'.comap (algebraMap ℤ (integralClosure ℤ ℂ))).IsPrime :=
      Ideal.IsPrime.comap _
    refine IsPrime.to_maximal_ideal (fun hbot => ?_)
    have hpmem : (p : ℤ) ∈ 𝔪'.comap (algebraMap ℤ (integralClosure ℤ ℂ)) := by
      rw [Ideal.mem_comap]
      simpa using hp𝔪'
    rw [hbot, Ideal.mem_bot] at hpmem
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpmem)
  have hcong : ∀ (t : T) (c : ℤ), χ t = χ c → ev t - (c : integralClosure ℤ ℂ) ∈ 𝔪' := by
    intro t c hχtc
    have htc𝔮 : Ideal.Quotient.mk 𝔭 (t - (c : T)) ∈ 𝔮 := by
      show red _ = 0
      rw [← RingHom.comp_apply, hred, map_sub, hχtc, sub_self]
    rw [← hevQ_comap, Ideal.mem_comap] at htc𝔮
    simpa [evQ, Ideal.Quotient.lift_mk, map_sub, map_intCast] using htc𝔮

  have heig_clause : ∀ (f' : Φ), f' ∈ spL → (∀ t, τ t f' = evℂ t • f') →
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
        heckeTLin w hℓ hℓM f' = (ev (opT ℓ hℓ hℓS hℓM) : ℂ) • f') ∧
      heckeULin w hpM f' = (ev opU : ℂ) • f' := by
    intro f' hf' hfeig
    have hagT : ∀ ℓ hℓ hℓS hℓM, ∀ g ∈ L, τ (opT ℓ hℓ hℓS hℓM) g = heckeTLin w hℓ hℓM g :=
      fun ℓ hℓ hℓS hℓM g hg =>
        (hτL (opT ℓ hℓ hℓS hℓM) ⟨g, hg⟩).trans (hopT ℓ hℓ hℓS hℓM ⟨g, hg⟩)
    have hagU : ∀ g ∈ L, τ opU g = heckeULin w hpM g :=
      fun g hg => (hτL opU ⟨g, hg⟩).trans (hopU ⟨g, hg⟩)
    refine ⟨fun ℓ hℓ hℓS hℓM => ?_, ?_⟩
    · rw [hev_coe, ← hfeig (opT ℓ hℓ hℓS hℓM)]
      exact (extAgree (τ _) (heckeTLin w hℓ hℓM) (hagT ℓ hℓ hℓS hℓM) hf').symm
    · rw [hev_coe, ← hfeig opU]
      exact (extAgree (τ opU) (heckeULin w hpM) hagU hf').symm

  obtain ⟨f, hfsp, hf1, hf2, hfeig⟩ :
      ∃ f : Φ, f ∈ spL ∧
        (∀ n, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n) ∧
        (∃ (n : ℕ) (x y : integralClosure ℤ ℂ), y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n ∧ x ∉ 𝔪') ∧
        (∀ t : T, τ t f = evℂ t • f) := by

    obtain ⟨c, _, hcsum⟩ := Submodule.mem_span_finset.mp f₀.2

    haveI hQbarAlgbc : Algebra.IsAlgebraic ℚ ↥Qbar := algebraicClosure.isAlgebraic ℚ ℂ
    have hcalg : ∀ y : Φ, IsAlgebraic ℤ (c y : ℂ) := fun y =>
      (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr
        ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (c y : Qbar)).algebraMap)
    choose Ny hNy0 hNyint using fun y => (hcalg y).exists_integral_multiple
    let N : ℤ := ∏ y ∈ orbitGen, Ny y
    have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y _ => hNy0 y
    have hNcint : ∀ y ∈ orbitGen, IsIntegral ℤ ((N : ℂ) * (c y : ℂ)) := by
      intro y hy
      have hNfact : (N : ℂ) = ((orbitGen.erase y).prod Ny : ℤ) * (Ny y : ℂ) := by
        have h : N = (orbitGen.erase y).prod Ny * Ny y :=
          (Finset.prod_erase_mul orbitGen Ny hy).symm
        push_cast [h]; ring
      rw [hNfact, mul_assoc, show (Ny y : ℂ) * (c y : ℂ) = Ny y • (c y : ℂ) from
        (zsmul_eq_mul ..).symm]
      exact isIntegral_algebraMap.mul (hNyint y)

    let f₁ : Φ := (N : ℂ) • (↑f₀ : Φ)
    have hf₁sp : f₁ ∈ spL := spL.smul_mem _ hf₀sp
    have hf₁ne : f₁ ≠ 0 := smul_ne_zero (by exact_mod_cast hN0) hf₀ne'
    have hf₁eig : ∀ t, τ t f₁ = evℂ t • f₁ := fun t => by
      simp only [f₁, (τ t).map_smul, hevℂ t, smul_comm (N : ℂ) (evℂ t)]

    have hf₁coeff : ∀ n, qCoeff f₁ n = ∑ y ∈ orbitGen, ((N : ℂ) * (c y : ℂ)) * qCoeff y n :=
      fun n => by
        rw [show (f₁ : Φ) = (N : ℂ) • ∑ y ∈ orbitGen, c y • y from by rw [hcsum]]
        exact qCoeff_smul_finset_sum_smul' Qbar orbitGen c (N : ℂ) n

    have horbit_L : ∀ y ∈ orbitGen, y ∈ L := by
      intro y hy
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hy
      exact (g • x).2
    have haint : ∀ n, ∃ z : integralClosure ℤ ℂ, (z : ℂ) = qCoeff f₁ n := by
      intro n; rw [hf₁coeff]
      have hmem : (∑ y ∈ orbitGen, (N : ℂ) * (c y : ℂ) * qCoeff y n) ∈ integralClosure ℤ ℂ := by
        refine Subalgebra.sum_mem _ fun y hy => Subalgebra.mul_mem _ (hNcint y hy) ?_
        obtain ⟨z, hz⟩ := (hLcoeff _ (horbit_L y hy) n).1
        exact hz ▸ z.2
      exact ⟨⟨_, hmem⟩, rfl⟩

    have haE : ∃ E : IntermediateField ℚ ℂ, FiniteDimensional ℚ E ∧ ∀ n, qCoeff f₁ n ∈ E := by
      obtain ⟨E, hEfd, hEmem⟩ :=
        exists_intermediateField_finiteDimensional_sum_mem K orbitGen
          (fun y => (N : ℂ) * (c y : ℂ)) hNcint (fun y n => qCoeff y n)
          (fun y hy n => (hLcoeff _ (horbit_L y hy) n).2)
      exact ⟨E, hEfd, fun n => hf₁coeff n ▸ hEmem n⟩
    have hne : ∃ n, qCoeff f₁ n ≠ 0 := by
      by_contra hall; push Not at hall
      exact hf₁ne (eq_zero_of_qCoeff_eq_zero _ hall)

    obtain ⟨E, hEfd, haE⟩ := haE
    haveI := hEfd
    obtain ⟨c', hc'1, hc'2⟩ := exists_rescale_local_unit E 𝔪' h𝔪'pr
      (Fact.out : p.Prime) hp𝔪' (fun n => qCoeff f₁ n) haE haint hne
    refine ⟨c' • f₁, spL.smul_mem _ hf₁sp,
      fun n => by rw [qCoeff_smul _ _ _]; exact hc'1 n,
      ?_,
      fun t => by simp only [(τ t).map_smul, hf₁eig t, smul_comm c' (evℂ t)]⟩
    obtain ⟨n, xx, yy, hyy, hxy, hxx⟩ := hc'2
    exact ⟨n, xx, yy, hyy, by rw [qCoeff_smul _ _ _]; exact hxy, hxx⟩
  obtain ⟨heig3, heig4⟩ := heig_clause f hfsp hfeig
  exact ⟨𝔪', h𝔪'max, hp𝔪', f, hf1, hf2,
    fun ℓ hℓ hℓS hℓM => ⟨ev (opT ℓ hℓ hℓS hℓM), hcong _ _ (hχT ℓ hℓ hℓS hℓM), heig3 ℓ hℓ hℓS hℓM⟩,
    ⟨ev opU, hcong _ _ hχU, heig4⟩⟩

end DSOut

private noncomputable def residualCharacter {T : Type} [CommRing T] {k : Type} [CommRing k]
    (𝔐 : Ideal T) (ψ : ℤ →+* k)
    (hall : ∀ t : T, ∃ c : ℤ, t - (c : T) ∈ 𝔐)
    (hker : ∀ m : ℤ, ((m : ℤ) : T) ∈ 𝔐 → ψ m = 0) : T →+* k where
  toFun t := ψ (hall t).choose
  map_one' := by
    have h := residualCharacter.congr_aux 𝔐 ψ hall hker 1 1 (by simp)
    simpa using h
  map_mul' := by
    intro x y
    have hx := (hall x).choose_spec
    have hy := (hall y).choose_spec
    have hxy : x * y - (((hall x).choose * (hall y).choose : ℤ) : T) ∈ 𝔐 := by
      have hid : x * y - (((hall x).choose * (hall y).choose : ℤ) : T) =
          x * (y - ((hall y).choose : T)) + ((hall y).choose : T) * (x - ((hall x).choose : T)) := by
        push_cast
        ring
      rw [hid]
      exact 𝔐.add_mem (𝔐.mul_mem_left _ hy) (𝔐.mul_mem_left _ hx)
    have h := residualCharacter.congr_aux 𝔐 ψ hall hker (x * y) _ hxy
    rw [h, map_mul]
  map_zero' := by
    have h := residualCharacter.congr_aux 𝔐 ψ hall hker 0 0 (by simp)
    simpa using h
  map_add' := by
    intro x y
    have hx := (hall x).choose_spec
    have hy := (hall y).choose_spec
    have hxy : x + y - (((hall x).choose + (hall y).choose : ℤ) : T) ∈ 𝔐 := by
      have hid : x + y - (((hall x).choose + (hall y).choose : ℤ) : T) =
          (x - ((hall x).choose : T)) + (y - ((hall y).choose : T)) := by
        push_cast
        ring
      rw [hid]
      exact 𝔐.add_mem hx hy
    have h := residualCharacter.congr_aux 𝔐 ψ hall hker (x + y) _ hxy
    rw [h, map_add]

end RC1

open RC1 in
open RC1.LatticeAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 25600000 in

theorem solution (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (w : ℤ) (S : Set ℕ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) w) (hFK : ∀ n : ℕ, qCoeff F n ∈ K)
    (hFint : ∀ n : ℕ, ∃ x : integralClosure ℤ ℂ, (x : ℂ) = qCoeff F n)
    (hFne : ∃ (n : ℕ) (x : integralClosure ℤ ℂ), (x : ℂ) = qCoeff F n ∧ x ∉ 𝔪)
    (cT : ℕ → ℤ) (cU : ℤ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (n : ℕ) (x x' : integralClosure ℤ ℂ),
      (x : ℂ) = qCoeff (heckeTLin w hℓ hℓM F) n → (x' : ℂ) = qCoeff F n → x - cT ℓ * x' ∈ 𝔪)
    (hU : ∀ (n : ℕ) (x x' : integralClosure ℤ ℂ),
      (x : ℂ) = qCoeff (heckeULin w hpM F) n → (x' : ℂ) = qCoeff F n → x - cU * x' ∈ 𝔪) :
    ∃ 𝔪' : Ideal (integralClosure ℤ ℂ), 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 M) w,
      (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n) ∧
      (∃ (n : ℕ) (x y : integralClosure ℤ ℂ), y ∉ 𝔪' ∧ (x : ℂ) = y * qCoeff f n ∧ x ∉ 𝔪') ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
        ∃ lam : integralClosure ℤ ℂ, lam - cT ℓ ∈ 𝔪' ∧ heckeTLin w hℓ hℓM f = (lam : ℂ) • f) ∧
      (∃ α : integralClosure ℤ ℂ, α - cU ∈ 𝔪' ∧ heckeULin w hpM f = (α : ℂ) • f) := by

  by_cases hw0 : w ≤ 0
  case pos =>
    exfalso
    obtain ⟨n, x, hx, hxm⟩ := hFne
    have hF0 : ⇑F = 0 := nonpos_coe_eq_zero hw0 F
    have hq0 : qCoeff (⇑F) n = 0 := by
      rw [hF0, show (0 : UpperHalfPlane → ℂ)
          = ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 M) w) by simp]
      exact qCoeff_zero' n
    have hxc : (x : ℂ) = ((0 : integralClosure ℤ ℂ) : ℂ) := by
      rw [hx, hq0]
      simp
    have hx0 : x = 0 := Subtype.coe_injective hxc
    exact hxm (hx0 ▸ 𝔪.zero_mem)
  case neg =>
  have hw1 : (0 : ℤ) < w := not_le.mp hw0

  obtain ⟨L, hLmem, hLfin, hLT, hLU⟩ := exists_coeffLattice M w (by omega) K
  haveI : Module.Finite ℤ ↥L := hLfin
  haveI := isTorsionFree_submodule L
  haveI : Module.Free ℤ ↥L := Module.free_of_finite_type_torsion_free'
  have hFL : F ∈ L := (hLmem F).mpr fun n => ⟨hFint n, hFK n⟩

  set U' : Module.End ℤ ↥L :=
    ((heckeULin w hpM).restrictScalars ℤ).restrict (hLU p hpM) with hU'def
  set 𝒮 : Set (Module.End ℤ ↥L) :=
    {U'} ∪ ⋃ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
      {((heckeTLin w hℓ hℓM).restrictScalars ℤ).restrict (hLT ℓ hℓ hℓM)} with h𝒮def
  have hcomm : ∀ a ∈ 𝒮, ∀ b ∈ 𝒮, a * b = b * a := by
    have hmem : ∀ a ∈ 𝒮, a = U' ∨ ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M),
        a = ((heckeTLin w hℓ hℓM).restrictScalars ℤ).restrict (hLT ℓ hℓ hℓM) := by
      intro a ha
      rw [h𝒮def] at ha
      rcases ha with ha | ha
      · exact Or.inl ha
      · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at ha
        obtain ⟨ℓ, hℓ, _, hℓM, rfl⟩ := ha
        exact Or.inr ⟨ℓ, hℓ, hℓM, rfl⟩
    intro a ha b hb
    rcases hmem a ha with rfl | ⟨ℓ, hℓ, hℓM, rfl⟩ <;> rcases hmem b hb with rfl | ⟨ℓ', hℓ', hℓM', rfl⟩
    · rfl
    · exact ((restrict_commute L _ _ _ _
        ((CuspForm.heckeTLin_heckeULin_comm w hℓ' hℓM' hpM).symm)).eq)
    · exact ((restrict_commute L _ _ _ _
        (CuspForm.heckeTLin_heckeULin_comm w hℓ hℓM hpM)).eq)
    · exact ((restrict_commute L _ _ _ _
        (CuspForm.heckeTLin_comm w hℓ hℓM hℓ' hℓM')).eq)
  haveI : IsMulCommutative ↥(Algebra.adjoin ℤ 𝒮) := Algebra.isMulCommutative_adjoin ℤ hcomm
  letI : CommRing ↥(Algebra.adjoin ℤ 𝒮) := inferInstance

  haveI hEndFin : Module.Finite ℤ (Module.End ℤ ↥L) := inferInstance
  haveI hTfin : Module.Finite ℤ ↥(Algebra.adjoin ℤ 𝒮) := by
    have hfg : (Subalgebra.toSubmodule (Algebra.adjoin ℤ 𝒮)).FG :=
      IsNoetherian.noetherian (Subalgebra.toSubmodule (Algebra.adjoin ℤ 𝒮))
    exact Module.Finite.iff_fg.mpr hfg
  haveI hTtf : Module.IsTorsionFree ℤ ↥(Algebra.adjoin ℤ 𝒮) :=
    Subtype.val_injective.moduleIsTorsionFree _ (fun _ _ => rfl)

  haveI : IsScalarTower ℤ ↥(Algebra.adjoin ℤ 𝒮) ↥L := inferInstance
  haveI : Module.Finite ↥(Algebra.adjoin ℤ 𝒮) ↥L :=
    Module.Finite.of_restrictScalars_finite ℤ ↥(Algebra.adjoin ℤ 𝒮) ↥L
  haveI : FaithfulSMul ↥(Algebra.adjoin ℤ 𝒮) ↥L :=
    ⟨fun {t₁ t₂} h => Subtype.ext (LinearMap.ext fun v => h v)⟩

  have hw1' : (0 : ℤ) ≤ w - 1 := by omega
  have hlift : ∀ (g : ↥L) (n : ℕ), ∃ x : integralClosure ℤ ℂ,
      (x : ℂ) = qCoeff (↑g : CuspForm (CongruenceSubgroup.Gamma0 M) w) n :=
    fun g n => ((hLmem ↑g).mp g.2 n).1
  have hsm : ∀ (x : Module.End ℤ ↥L) (hx : x ∈ Algebra.adjoin ℤ 𝒮) (g : ↥L),
      (⟨x, hx⟩ : ↥(Algebra.adjoin ℤ 𝒮)) • g = x g := fun _ _ _ => rfl
  have h𝒮mem : ∀ y ∈ 𝒮, y = U' ∨ ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
      y = ((heckeTLin w hℓ hℓM).restrictScalars ℤ).restrict (hLT ℓ hℓ hℓM) := by
    intro y hy
    rw [h𝒮def] at hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨ℓ, hℓ, hℓS, hℓM, rfl⟩ := hy
      exact Or.inr ⟨ℓ, hℓ, hℓS, hℓM, rfl⟩

  have h𝒥T0 : ∀ (x : Module.End ℤ ↥L) (hx : x ∈ Algebra.adjoin ℤ 𝒮) (g : ↥L),
      (∀ (n : ℕ) (z : integralClosure ℤ ℂ), (z : ℂ) = qCoeff (↑g : CuspForm (CongruenceSubgroup.Gamma0 M) w) n → z ∈ 𝔪) →
      ∀ (n : ℕ) (z : integralClosure ℤ ℂ),
        (z : ℂ) = qCoeff (↑(x g) : CuspForm (CongruenceSubgroup.Gamma0 M) w) n → z ∈ 𝔪 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        intro g hg n z hz
        rcases h𝒮mem y hy with rfl | ⟨ℓ, hℓ, hℓS, hℓM, rfl⟩
        ·
          have hcoe : (↑(U' g) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
              = heckeULin w hpM ↑g := by
            rw [hU'def]
            rfl
          rw [hcoe, qCoeff_heckeULin _ (Fact.out : p.Prime).ne_zero hpM n] at hz
          obtain ⟨x₂, hx₂⟩ := hlift g (n * p)
          have hzx : z = x₂ := Subtype.coe_injective (by
            show (z : ℂ) = (x₂ : ℂ)
            rw [hz, hx₂])
          rw [hzx]
          exact hg _ x₂ hx₂
        ·
          have hcoe : (↑((((heckeTLin w hℓ hℓM).restrictScalars ℤ).restrict (hLT ℓ hℓ hℓM)) g) :
              CuspForm (CongruenceSubgroup.Gamma0 M) w) = heckeTLin w hℓ hℓM ↑g := rfl
          rw [hcoe, qCoeff_heckeTLin _ hℓ hℓM n] at hz
          obtain ⟨x₁, hx₁⟩ := hlift g (n * ℓ)
          by_cases hdvd : ℓ ∣ n
          · obtain ⟨x₂, hx₂⟩ := hlift g (n / ℓ)
            have hzx : z = x₁ + (ℓ : integralClosure ℤ ℂ) ^ (w - 1).toNat * x₂ := by
              apply Subtype.coe_injective
              show (z : ℂ) = _
              push_cast
              rw [hz, hx₁, hx₂, if_pos hdvd,
                show ((ℓ : ℂ) ^ (w - 1).toNat) = (ℓ : ℂ) ^ (w - 1) from by
                  rw [← zpow_natCast, Int.toNat_of_nonneg hw1']]
            rw [hzx]
            exact 𝔪.add_mem (hg _ x₁ hx₁) (𝔪.mul_mem_left _ (hg _ x₂ hx₂))
          · have hzx : z = x₁ := Subtype.coe_injective (by
              show (z : ℂ) = (x₁ : ℂ)
              rw [hz, hx₁, if_neg hdvd, add_zero])
            rw [hzx]
            exact hg _ x₁ hx₁
    | algebraMap r =>
        intro g hg n z hz
        rw [Module.algebraMap_end_apply] at hz
        have hcoe : (↑(r • g) : CuspForm (CongruenceSubgroup.Gamma0 M) w) = r • (↑g : CuspForm (CongruenceSubgroup.Gamma0 M) w) := rfl
        rw [hcoe, ← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul] at hz
        obtain ⟨x₂, hx₂⟩ := hlift g n
        have hzx : z = (r : integralClosure ℤ ℂ) * x₂ := by
          apply Subtype.coe_injective
          push_cast
          rw [hz, hx₂]
        rw [hzx]
        exact 𝔪.mul_mem_left _ (hg _ x₂ hx₂)
    | add y y' hy hy' ihy ihy' =>
        intro g hg n z hz
        rw [LinearMap.add_apply] at hz
        obtain ⟨x₁, hx₁⟩ := hlift (y g) n
        obtain ⟨x₂, hx₂⟩ := hlift (y' g) n
        have hzx : z = x₁ + x₂ := by
          apply Subtype.coe_injective
          push_cast
          rw [hz, hx₁, hx₂, show (↑(y g + y' g) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
              = ↑(y g) + ↑(y' g) from rfl]
          exact qCoeff_add _ _ n
        rw [hzx]
        exact 𝔪.add_mem (ihy g hg n x₁ hx₁) (ihy' g hg n x₂ hx₂)
    | mul y y' hy hy' ihy ihy' =>
        intro g hg n z hz
        rw [Module.End.mul_apply] at hz
        exact ihy (y' g) (fun m u hu => ihy' g hg m u hu) n z hz
  have h𝒥T : ∀ t : ↥(Algebra.adjoin ℤ 𝒮), ∀ g : ↥L,
      (∀ (n : ℕ) (z : integralClosure ℤ ℂ), (z : ℂ) = qCoeff (↑g : CuspForm (CongruenceSubgroup.Gamma0 M) w) n → z ∈ 𝔪) →
      ∀ (n : ℕ) (z : integralClosure ℤ ℂ),
        (z : ℂ) = qCoeff (↑(t • g) : CuspForm (CongruenceSubgroup.Gamma0 M) w) n → z ∈ 𝔪 :=
    fun t => h𝒥T0 t.1 t.2

  set P𝔪 : ↥L → Prop := fun g => ∀ (n : ℕ) (z : integralClosure ℤ ℂ),
    (z : ℂ) = qCoeff (↑g : CuspForm (CongruenceSubgroup.Gamma0 M) w) n → z ∈ 𝔪 with hPdef
  have hP0 : P𝔪 0 := by
    intro n z hz
    have hz0 : (z : ℂ) = ((0 : integralClosure ℤ ℂ) : ℂ) := by
      rw [hz, show ((0 : ↥L) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
          = (0 : CuspForm (CongruenceSubgroup.Gamma0 M) w) from rfl]
      rw [qCoeff_zero' n]
      simp
    rw [Subtype.coe_injective hz0]
    exact 𝔪.zero_mem
  have hPadd : ∀ {x y : ↥L}, P𝔪 x → P𝔪 y → P𝔪 (x + y) := by
    intro a b ha hb n z hz
    obtain ⟨x, hx⟩ := ((hLmem _).mp a.2 n).1
    obtain ⟨y, hy⟩ := ((hLmem _).mp b.2 n).1
    have hzxy : z = x + y := by
      apply Subtype.coe_injective
      push_cast
      rw [hz, hx, hy, show ((a + b : ↥L) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
          = (↑a + ↑b : CuspForm (CongruenceSubgroup.Gamma0 M) w) from rfl]
      exact qCoeff_add _ _ n
    rw [hzxy]
    exact 𝔪.add_mem (ha n x hx) (hb n y hy)
  set 𝔐 : Ideal ↥(Algebra.adjoin ℤ 𝒮) :=
    congrIdeal P𝔪 hP0 hPadd (fun t {g} hg => h𝒥T t g hg) ⟨F, hFL⟩ with h𝔐def

  have hqsub : ∀ (f g : CuspForm (CongruenceSubgroup.Gamma0 M) w) (n : ℕ),
      qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
    intro f g n
    rw [sub_eq_add_neg, qCoeff_add, qCoeff_neg]
    ring

  have hgen : ∀ (y : Module.End ℤ ↥L) (hy : y ∈ Algebra.adjoin ℤ 𝒮) (c : ℤ),
      (∀ (n : ℕ) (x x' : integralClosure ℤ ℂ),
        (x : ℂ) = qCoeff (↑(y (⟨F, hFL⟩ : ↥L)) : CuspForm (CongruenceSubgroup.Gamma0 M) w) n →
        (x' : ℂ) = qCoeff F n → x - c * x' ∈ 𝔪) →
      (⟨y, hy⟩ : ↥(Algebra.adjoin ℤ 𝒮)) - (c : ↥(Algebra.adjoin ℤ 𝒮)) ∈ 𝔐 := by
    intro y hy c hc
    rw [h𝔐def, mem_congrIdeal]
    intro n z hz
    obtain ⟨x, hx⟩ := hlift (y (⟨F, hFL⟩ : ↥L)) n
    obtain ⟨x', hx'⟩ := hlift (⟨F, hFL⟩ : ↥L) n
    have hz' : z = x - (c : integralClosure ℤ ℂ) * x' := by
      apply Subtype.coe_injective
      push_cast
      rw [hz, hx, hx']
      have hsub : ((⟨y, hy⟩ - (c : ↥(Algebra.adjoin ℤ 𝒮))) • (⟨F, hFL⟩ : ↥L))
          = y (⟨F, hFL⟩ : ↥L) - c • (⟨F, hFL⟩ : ↥L) := by
        rw [sub_smul, hsm,
          show ((c : ℤ) : ↥(Algebra.adjoin ℤ 𝒮)) • (⟨F, hFL⟩ : ↥L) = c • (⟨F, hFL⟩ : ↥L) from by
            rw [show ((c : ℤ) : ↥(Algebra.adjoin ℤ 𝒮)) = algebraMap ℤ _ c from rfl,
              algebraMap_smul]]
      rw [hsub, show (↑(y (⟨F, hFL⟩ : ↥L) - c • (⟨F, hFL⟩ : ↥L)) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
          = ↑(y (⟨F, hFL⟩ : ↥L)) - ↑(c • (⟨F, hFL⟩ : ↥L)) from rfl, hqsub]
      have hcs : (↑(c • (⟨F, hFL⟩ : ↥L)) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
          = (c : ℂ) • F := by
        rw [show (↑(c • (⟨F, hFL⟩ : ↥L)) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
            = c • (F : CuspForm (CongruenceSubgroup.Gamma0 M) w) from rfl,
          ← Int.cast_smul_eq_zsmul ℂ]
      rw [hcs, qCoeff_smul]
    rw [hz']
    exact hc n x x' hx hx'

  have hall0 : ∀ (x : Module.End ℤ ↥L) (hx : x ∈ Algebra.adjoin ℤ 𝒮),
      ∃ c : ℤ, (⟨x, hx⟩ : ↥(Algebra.adjoin ℤ 𝒮)) - (c : ↥(Algebra.adjoin ℤ 𝒮)) ∈ 𝔐 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        rcases h𝒮mem y hy with rfl | ⟨ℓ, hℓ, hℓS, hℓM, rfl⟩
        · refine ⟨cU, hgen _ _ cU ?_⟩
          intro n x x' hx hx'
          exact hU n x x' hx hx'
        · refine ⟨cT ℓ, hgen _ _ (cT ℓ) ?_⟩
          intro n x x' hx hx'
          exact hT ℓ hℓ hℓS hℓM n x x' hx hx'
    | algebraMap r =>
        refine ⟨r, ?_⟩
        have : ((algebraMap ℤ (Module.End ℤ ↥L) r : Module.End ℤ ↥L)) ∈ Algebra.adjoin ℤ 𝒮 :=
          Subalgebra.algebraMap_mem _ r
        have heq : (⟨algebraMap ℤ (Module.End ℤ ↥L) r, this⟩ : ↥(Algebra.adjoin ℤ 𝒮))
            = (r : ↥(Algebra.adjoin ℤ 𝒮)) := by
          apply Subtype.ext
          push_cast
          rfl
        rw [heq, sub_self]
        exact 𝔐.zero_mem
    | add y y' hy hy' ihy ihy' =>
        obtain ⟨c₁, hc₁⟩ := ihy
        obtain ⟨c₂, hc₂⟩ := ihy'
        refine ⟨c₁ + c₂, ?_⟩
        have hid : (⟨y + y', Subalgebra.add_mem _ hy hy'⟩ : ↥(Algebra.adjoin ℤ 𝒮))
            - ((c₁ + c₂ : ℤ) : ↥(Algebra.adjoin ℤ 𝒮))
            = ((⟨y, hy⟩ : ↥(Algebra.adjoin ℤ 𝒮)) - (c₁ : ↥(Algebra.adjoin ℤ 𝒮)))
              + ((⟨y', hy'⟩ : ↥(Algebra.adjoin ℤ 𝒮)) - (c₂ : ↥(Algebra.adjoin ℤ 𝒮))) := by
          have h1 : (⟨y + y', Subalgebra.add_mem _ hy hy'⟩ : ↥(Algebra.adjoin ℤ 𝒮))
              = ⟨y, hy⟩ + ⟨y', hy'⟩ := rfl
          rw [h1]
          push_cast
          ring
        rw [hid]
        exact 𝔐.add_mem hc₁ hc₂
    | mul y y' hy hy' ihy ihy' =>
        obtain ⟨c₁, hc₁⟩ := ihy
        obtain ⟨c₂, hc₂⟩ := ihy'
        refine ⟨c₁ * c₂, ?_⟩
        have hid : (⟨y * y', Subalgebra.mul_mem _ hy hy'⟩ : ↥(Algebra.adjoin ℤ 𝒮))
            - ((c₁ * c₂ : ℤ) : ↥(Algebra.adjoin ℤ 𝒮))
            = (⟨y, hy⟩ : ↥(Algebra.adjoin ℤ 𝒮)) * ((⟨y', hy'⟩ : ↥(Algebra.adjoin ℤ 𝒮)) - (c₂ : ↥(Algebra.adjoin ℤ 𝒮)))
              + (c₂ : ↥(Algebra.adjoin ℤ 𝒮)) * ((⟨y, hy⟩ : ↥(Algebra.adjoin ℤ 𝒮)) - (c₁ : ↥(Algebra.adjoin ℤ 𝒮))) := by
          have h1 : (⟨y * y', Subalgebra.mul_mem _ hy hy'⟩ : ↥(Algebra.adjoin ℤ 𝒮))
              = ⟨y, hy⟩ * ⟨y', hy'⟩ := rfl
          rw [h1]
          push_cast
          ring
        rw [hid]
        exact 𝔐.add_mem (Ideal.mul_mem_left _ _ hc₂) (Ideal.mul_mem_left _ _ hc₁)
  have hall : ∀ t : ↥(Algebra.adjoin ℤ 𝒮), ∃ c : ℤ, t - (c : ↥(Algebra.adjoin ℤ 𝒮)) ∈ 𝔐 :=
    fun t => hall0 t.1 t.2

  letI : Field (integralClosure ℤ ℂ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  set ψ : ℤ →+* (integralClosure ℤ ℂ ⧸ 𝔪) :=
    (Ideal.Quotient.mk 𝔪).comp (Int.castRingHom (integralClosure ℤ ℂ)) with hψdef

  have hker : ∀ m : ℤ, ((m : ℤ) : ↥(Algebra.adjoin ℤ 𝒮)) ∈ 𝔐 → ψ m = 0 := by
    intro m hm
    rw [h𝔐def, mem_congrIdeal] at hm
    obtain ⟨n₀, x₀, hx₀, hx₀m⟩ := hFne
    have hsm' : ((m : ↥(Algebra.adjoin ℤ 𝒮)) • (⟨F, hFL⟩ : ↥L)) = m • (⟨F, hFL⟩ : ↥L) := by
      rw [show ((m : ℤ) : ↥(Algebra.adjoin ℤ 𝒮)) = algebraMap ℤ _ m from rfl,
        algebraMap_smul]
    have hmem := hm n₀ ((m : integralClosure ℤ ℂ) * x₀) (by
      push_cast
      rw [hx₀, hsm']
      have hcoe : (↑(m • (⟨F, hFL⟩ : ↥L)) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
          = (m : ℂ) • F := by
        rw [show (↑(m • (⟨F, hFL⟩ : ↥L)) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
            = m • (F : CuspForm (CongruenceSubgroup.Gamma0 M) w) from rfl,
          ← Int.cast_smul_eq_zsmul ℂ]
      rw [hcoe, qCoeff_smul])
    have hmm : (m : integralClosure ℤ ℂ) ∈ 𝔪 := by
      rcases (h𝔪.isPrime.mem_or_mem hmem) with h | h
      · exact h
      · exact absurd h hx₀m
    show (Ideal.Quotient.mk 𝔪) ((m : ℤ) : integralClosure ℤ ℂ) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmm
  set χ : ↥(Algebra.adjoin ℤ 𝒮) →+* (integralClosure ℤ ℂ ⧸ 𝔪) :=
    residualCharacter 𝔐 ψ hall hker with hχdef

  obtain ⟨𝔭, h𝔭min, h𝔭ker, h𝔭faith, h𝔭char, ⟨red, hred⟩, x, hx0, hxkill, hxann⟩ :=
    DeligneSerre.exists_charZero_eigenvector_of_residual_character (M := ↥L) χ

  have hU'mem : U' ∈ Algebra.adjoin ℤ 𝒮 :=
    Algebra.subset_adjoin (by rw [h𝒮def]; exact Or.inl rfl)
  have hTmem : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
      ((heckeTLin w hℓ hℓM).restrictScalars ℤ).restrict (hLT ℓ hℓ hℓM) ∈ Algebra.adjoin ℤ 𝒮 := by
    intro ℓ hℓ hℓS hℓM
    refine Algebra.subset_adjoin ?_
    rw [h𝒮def]
    right
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨ℓ, hℓ, hℓS, hℓM, rfl⟩

  set opU : ↥(Algebra.adjoin ℤ 𝒮) := ⟨U', hU'mem⟩ with hopUdef
  have hopU : ∀ g : ↥L, (↑(opU • g) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
      = heckeULin w hpM ↑g := fun g => rfl
  have hopT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (g : ↥L),
      (↑((⟨_, hTmem ℓ hℓ hℓS hℓM⟩ : ↥(Algebra.adjoin ℤ 𝒮)) • g) :
        CuspForm (CongruenceSubgroup.Gamma0 M) w) = heckeTLin w hℓ hℓM ↑g := fun _ _ _ _ _ => rfl

  have hTlin0 : ∀ (x : Module.End ℤ ↥L) (hx : x ∈ Algebra.adjoin ℤ 𝒮),
      ∃ τ : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) w),
        ∀ g : ↥L, (↑(x g) : CuspForm (CongruenceSubgroup.Gamma0 M) w) = τ ↑g := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        rcases h𝒮mem y hy with rfl | ⟨ℓ, hℓ, hℓS, hℓM, rfl⟩
        · exact ⟨heckeULin w hpM, fun g => rfl⟩
        · exact ⟨heckeTLin w hℓ hℓM, fun g => rfl⟩
    | algebraMap r =>
        refine ⟨r • (1 : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) w)), fun g => ?_⟩
        rw [Module.algebraMap_end_apply]
        show ((r • g : ↥L) : CuspForm (CongruenceSubgroup.Gamma0 M) w) = _
        rw [show ((r • g : ↥L) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
            = r • (↑g : CuspForm (CongruenceSubgroup.Gamma0 M) w) from rfl]
        rw [LinearMap.smul_apply, Module.End.one_apply]
    | add y y' hy hy' ihy ihy' =>
        obtain ⟨τ₁, h₁⟩ := ihy
        obtain ⟨τ₂, h₂⟩ := ihy'
        refine ⟨τ₁ + τ₂, fun g => ?_⟩
        rw [LinearMap.add_apply]
        rw [show ((y g + y' g : ↥L) : CuspForm (CongruenceSubgroup.Gamma0 M) w)
            = ↑(y g) + ↑(y' g) from rfl, h₁ g, h₂ g]
        rfl
    | mul y y' hy hy' ihy ihy' =>
        obtain ⟨τ₁, h₁⟩ := ihy
        obtain ⟨τ₂, h₂⟩ := ihy'
        refine ⟨τ₁ * τ₂, fun g => ?_⟩
        rw [Module.End.mul_apply, h₁ (y' g), h₂ g]
        rfl
  have hTlin : ∀ t : ↥(Algebra.adjoin ℤ 𝒮),
      ∃ τ : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) w),
        ∀ g : ↥L, (↑(t • g) : CuspForm (CongruenceSubgroup.Gamma0 M) w) = τ ↑g :=
    fun t => hTlin0 t.1 t.2

  have h𝔐U : opU - (cU : ↥(Algebra.adjoin ℤ 𝒮)) ∈ 𝔐 :=
    hgen U' hU'mem cU (fun n x x' hx hx' => hU n x x' hx hx')
  have h𝔐T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
      (⟨_, hTmem ℓ hℓ hℓS hℓM⟩ : ↥(Algebra.adjoin ℤ 𝒮)) - (cT ℓ : ↥(Algebra.adjoin ℤ 𝒮)) ∈ 𝔐 :=
    fun ℓ hℓ hℓS hℓM => hgen _ (hTmem ℓ hℓ hℓS hℓM) (cT ℓ)
      (fun n x x' hx hx' => hT ℓ hℓ hℓS hℓM n x x' hx hx')
  have hχint : ∀ c : ℤ, χ ((c : ℤ) : ↥(Algebra.adjoin ℤ 𝒮)) = ψ c := by
    intro c
    exact residualCharacter.congr_aux 𝔐 ψ hall hker _ c (by rw [sub_self]; exact 𝔐.zero_mem)
  have hχU : χ opU = ψ cU :=
    residualCharacter.congr_aux 𝔐 ψ hall hker opU cU h𝔐U
  have hχT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
      χ (⟨_, hTmem ℓ hℓ hℓS hℓM⟩ : ↥(Algebra.adjoin ℤ 𝒮)) = ψ (cT ℓ) :=
    fun ℓ hℓ hℓS hℓM => residualCharacter.congr_aux 𝔐 ψ hall hker _ (cT ℓ) (h𝔐T ℓ hℓ hℓS hℓM)
  have hχp : χ (((p : ℕ) : ℤ) : ↥(Algebra.adjoin ℤ 𝒮)) = 0 := by
    rw [hχint]
    show (Ideal.Quotient.mk 𝔪) (((p : ℕ) : ℤ) : integralClosure ℤ ℂ) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact_mod_cast hp𝔪

  refine DSOut.construct_output hpM S cT cU K L (fun g hg n => (hLmem g).mp hg n)
    hTlin (fun ℓ hℓ hℓS hℓM => ⟨_, hTmem ℓ hℓ hℓS hℓM⟩) opU hopT hopU χ ?_ ?_ ?_
    𝔭 h𝔭min h𝔭ker red hred x hx0 hxkill hxann.1
  ·
    have h := hχp
    rwa [show (((p : ℕ) : ℤ) : ↥(Algebra.adjoin ℤ 𝒮)) = ((p : ℕ) : ↥(Algebra.adjoin ℤ 𝒮))
      from by push_cast; rfl] at h
  · intro ℓ hℓ hℓS hℓM
    exact (hχT ℓ hℓ hℓS hℓM).trans (hχint (cT ℓ)).symm
  · exact hχU.trans (hχint cU).symm

end S_CuspForm_exists_eigenform_qCoeff_congr_of_heckeT_sub_mem
end P2MW
export P2MW.S_CuspForm_exists_eigenform_qCoeff_congr_of_heckeT_sub_mem (solution)
