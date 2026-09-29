-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.nonempty_of_isNilpotent_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1c714a09-2cf5-5130-b71c-bb1472f35caa

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_nonempty_of_isNilpotent_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace B25N3

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

noncomputable def intCoord (v : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (i : Fin 2) : ℤ_[p] :=
  ((mem_stdLattice ℤ_[p] ℚ_[p]).mp v.2 i).choose

theorem algebraMap_intCoord (v : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (i : Fin 2) :
    algebraMap ℤ_[p] ℚ_[p] (intCoord p v i) = (v : Fin 2 → ℚ_[p]) i :=
  ((mem_stdLattice ℤ_[p] ℚ_[p]).mp v.2 i).choose_spec

theorem intCoord_add (v w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (i : Fin 2) :
    intCoord p (v + w) i = intCoord p v i + intCoord p w i := by
  apply IsFractionRing.injective ℤ_[p] ℚ_[p]
  rw [map_add, algebraMap_intCoord, algebraMap_intCoord, algebraMap_intCoord, Submodule.coe_add, Pi.add_apply]

theorem intCoord_smul (r : ℤ_[p]) (v : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (i : Fin 2) :
    intCoord p (r • v) i = r * intCoord p v i := by
  apply IsFractionRing.injective ℤ_[p] ℚ_[p]
  rw [map_mul, algebraMap_intCoord, algebraMap_intCoord, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]

variable {κ : Type} [Field κ] [Algebra ℤ_[p] κ]

noncomputable def coordRed (i : Fin 2) : κ ⊗[ℤ_[p]] ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 →ₗ[κ] κ :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b =>
        { toFun := fun v => b * algebraMap ℤ_[p] κ (intCoord p v i)
          map_add' := fun v w => by rw [intCoord_add, map_add, mul_add]
          map_smul' := fun r v => by
            rw [intCoord_smul, map_mul, RingHom.id_apply, Algebra.smul_def, mul_left_comm] }
      map_add' := fun a b => by ext v; simp [add_mul]
      map_smul' := fun a b => by ext v; simp [mul_assoc] }

theorem coordRed_tmul (i : Fin 2) (b : κ) (v : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) :
    coordRed p (κ := κ) i (b ⊗ₜ[ℤ_[p]] v) = b * algebraMap ℤ_[p] κ (intCoord p v i) :=
  TensorProduct.AlgebraTensorModule.lift_tmul _ b v

theorem intCoord_stdBasisVec (i j : Fin 2) :
    intCoord p (stdBasisVec ℚ_[p] j) i = if i = j then 1 else 0 := by
  apply IsFractionRing.injective ℤ_[p] ℚ_[p]
  rw [algebraMap_intCoord]
  show (Pi.single j (1 : ℚ_[p]) : Fin 2 → ℚ_[p]) i = _
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]; simp [h]

end B25N3

namespace B25N3

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev pu : ℚ_[p]ˣ := unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero

theorem coe_pu : ((pu p : ℚ_[p]ˣ) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) := unitOfNeZero_coe _

noncomputable abbrev Lone : FullLattice ℤ_[p] ℚ_[p] := FullLattice.act (scalarGL (pu p)⁻¹) (stdFullLattice ℚ_[p])

theorem mem_Lone_iff (v : Fin 2 → ℚ_[p]) :
    v ∈ (Lone p).1 ↔ algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ stdLattice ℤ_[p] ℚ_[p] := by
  show v ∈ latticeMap (scalarGL (pu p)⁻¹) (stdLattice ℤ_[p] ℚ_[p]) ↔ _
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [smul_smul, ← coe_pu, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (pu p).ne_zero, one_smul]
  · intro hv
    exact ⟨_, hv, by rw [smul_smul, ← coe_pu, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (pu p).ne_zero, one_smul]⟩

theorem std_le_Lone : (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 ≤ (Lone p).1 := by
  intro v hv
  rw [mem_Lone_iff]
  exact (stdLattice ℤ_[p] ℚ_[p]).smul_mem _ hv

theorem smul_mem_std_of_mem_Lone (v : Fin 2 → ℚ_[p]) (hv : v ∈ (Lone p).1) :
    algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 :=
  (mem_Lone_iff p v).mp hv

theorem exists_eq_smul_of_dvd (w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) (h : ∀ i, (p : ℤ_[p]) ∣ intCoord p w i) :
    ∃ w' : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1,
      (w : Fin 2 → ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • (w' : Fin 2 → ℚ_[p]) := by
  choose b hb using h
  refine ⟨⟨fun i => algebraMap ℤ_[p] ℚ_[p] (b i), fun i => ⟨b i, rfl⟩⟩, ?_⟩
  funext i
  rw [Pi.smul_apply, smul_eq_mul, ← map_mul, ← hb, algebraMap_intCoord]

end B25N3

namespace B25NE

open B25N3

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev Lodd : FullLattice ℤ_[p] ℚ_[p] := FullLattice.act (diagSnd (pu p)⁻¹) (stdFullLattice ℚ_[p])

theorem hasDetIndex_Lodd : HasDetIndex (p : ℤ_[p]) (Lodd p).1 (-1) := by
  refine ⟨diagSnd (pu p)⁻¹, rfl, 1, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, map_one, one_mul, zpow_neg_one, ← coe_pu,
    ← Units.val_inv_eq_inv_val]
  show (Matrix.diagonal ![(1 : ℚ_[p]), (((pu p)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])]).det = _
  rw [Matrix.det_diagonal]; simp [Fin.prod_univ_two]

noncomputable def ω : ↥(Lodd p).1 ≃ₗ[ℤ_[p]] ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 :=
  (latticeMapEquiv (diagSnd (pu p)⁻¹) (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1).symm

theorem coe_ω_symm (w : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) :
    (((ω p).symm w : ↥(Lodd p).1) : Fin 2 → ℚ_[p]) =
      Matrix.mulVec ((diagSnd (pu p)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) (w : Fin 2 → ℚ_[p]) := by
  show ((latticeMapEquiv (diagSnd (pu p)⁻¹) _ w : ↥(Lodd p).1) : Fin 2 → ℚ_[p]) = _
  rw [coe_latticeMapEquiv_apply]

variable {B : Type} [CommRing B] [Algebra ℤ_[p] B] (θ : B)

noncomputable def U : ↥(Lodd p).1 →ₗ[ℤ_[p]] B where
  toFun v := algebraMap ℤ_[p] B (intCoord p (ω p v) 0) - θ * algebraMap ℤ_[p] B (intCoord p (ω p v) 1)
  map_add' v w := by rw [map_add, intCoord_add, intCoord_add, map_add, map_add]; ring
  map_smul' r v := by
    rw [map_smul, intCoord_smul, intCoord_smul, map_mul, map_mul, RingHom.id_apply, Algebra.smul_def]; ring

theorem U_apply (v : ↥(Lodd p).1) :
    U p θ v = algebraMap ℤ_[p] B (intCoord p (ω p v) 0) - θ * algebraMap ℤ_[p] B (intCoord p (ω p v) 1) := rfl

noncomputable def ux (x : PrimeSpectrum B) :
    latticeBaseChange ℤ_[p] ℚ_[p] (locRing B x) (Lodd p) →ₗ[locRing B x] stalk B x B :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b =>
        { toFun := fun v => b • LocalizedModule.mkLinearMap x.asIdeal.primeCompl B (U p θ v)
          map_add' := fun v w => by rw [map_add, map_add, smul_add]
          map_smul' := fun r v => by
            rw [map_smul, RingHom.id_apply, LinearMap.map_smul_of_tower, smul_comm] }
      map_add' := fun a b => LinearMap.ext fun v => add_smul a b _
      map_smul' := fun a b => LinearMap.ext fun v => smul_assoc a b _ }

theorem ux_tmul (x : PrimeSpectrum B) (b : locRing B x) (v : ↥(Lodd p).1) :
    ux p θ x (b ⊗ₜ[ℤ_[p]] v) = b • LocalizedModule.mk (U p θ v) 1 :=
  TensorProduct.AlgebraTensorModule.lift_tmul _ b v

end B25NE

namespace B25NE

open B25N3

variable (p : ℕ) [Fact p.Prime]

theorem map_pow_p {R : Type} [CommRing R] (φ : ℤ_[p] →+* R) (hφ : φ (p : ℤ_[p]) = 0) (a : ℤ_[p]) :
    (φ a) ^ p = φ a := by
  have hmem : a ^ p - a ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card,
      sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  have : φ (a ^ p - a) = 0 := by rw [← hb, map_mul, hφ, mul_zero]
  rwa [map_sub, map_pow, sub_eq_zero] at this

theorem dvd_of_map_eq_zero {R : Type} [CommRing R] [Nontrivial R] (φ : ℤ_[p] →+* R) {a : ℤ_[p]} (ha : φ a = 0) :
    (p : ℤ_[p]) ∣ a := by
  have hle := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
  have : a ∈ IsLocalRing.maximalIdeal ℤ_[p] := hle ((RingHom.mem_ker).mpr ha)
  rw [PadicInt.maximalIdeal_eq_span_p] at this
  exact Ideal.mem_span_singleton.mp this

theorem coe_eq_mulVec_ω (v : ↥(Lodd p).1) :
    (v : Fin 2 → ℚ_[p]) = Matrix.mulVec ((diagSnd (pu p)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) :
      Matrix (Fin 2) (Fin 2) ℚ_[p]) (fun i => algebraMap ℤ_[p] ℚ_[p] (intCoord p (ω p v) i)) := by
  conv_lhs => rw [← (ω p).symm_apply_apply v]
  rw [coe_ω_symm]
  congr 1
  funext i
  rw [algebraMap_intCoord]

variable {B : Type} [CommRing B] [Algebra ℤ_[p] B]

theorem exists_of_U_mem (θ : B) (hθ : IsUnit (θ ^ p - θ)) (x : PrimeSpectrum B) (hpx : (algebraMap ℤ_[p] B (p : ℤ_[p])) ∈ x.asIdeal)
    (v : ↥(Lodd p).1) (h : U p θ v ∈ x.asIdeal) :
    ∃ w ∈ (Lodd p).1, (v : Fin 2 → ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w := by
  set φ : ℤ_[p] →+* B ⧸ x.asIdeal := (Ideal.Quotient.mk x.asIdeal).comp (algebraMap ℤ_[p] B) with hφ
  have hφp : φ (p : ℤ_[p]) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpx
  haveI : Nontrivial (B ⧸ x.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr x.isPrime.ne_top
  set θb := Ideal.Quotient.mk x.asIdeal θ with hθb
  have hrel : φ (intCoord p (ω p v) 0) = θb * φ (intCoord p (ω p v) 1) := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [U_apply, map_sub, map_mul, sub_eq_zero] at this
    exact this
  have hunit : IsUnit (θb ^ p - θb) := by
    have := hθ.map (Ideal.Quotient.mk x.asIdeal)
    rwa [map_sub, map_pow] at this
  have h1 : φ (intCoord p (ω p v) 1) = 0 := by
    have e := hrel
    rw [← map_pow_p p φ hφp (intCoord p (ω p v) 0), hrel, mul_pow, map_pow_p p φ hφp] at e

    have : (θb ^ p - θb) * φ (intCoord p (ω p v) 1) = 0 := by rw [sub_mul, e, sub_self]
    exact (hunit.mul_right_eq_zero).mp this
  have h0 : φ (intCoord p (ω p v) 0) = 0 := by rw [hrel, h1, mul_zero]
  obtain ⟨c0, hc0⟩ := dvd_of_map_eq_zero p φ h0
  obtain ⟨c1, hc1⟩ := dvd_of_map_eq_zero p φ h1
  refine ⟨Matrix.mulVec ((diagSnd (pu p)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      (fun i => algebraMap ℤ_[p] ℚ_[p] (![c0, c1] i)), ?_, ?_⟩
  · exact mulVec_mem_latticeMap (fun i => ⟨_, rfl⟩)
  · rw [coe_eq_mulVec_ω, ← Matrix.mulVec_smul]
    congr 1
    funext i
    fin_cases i
    · show algebraMap ℤ_[p] ℚ_[p] (intCoord p (ω p v) 0) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • algebraMap ℤ_[p] ℚ_[p] c0
      rw [hc0, map_mul, smul_eq_mul]
    · show algebraMap ℤ_[p] ℚ_[p] (intCoord p (ω p v) 1) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • algebraMap ℤ_[p] ℚ_[p] c1
      rw [hc1, map_mul, smul_eq_mul]

theorem U_e0 (θ : B) : U p θ ((ω p).symm (stdBasisVec ℚ_[p] 0)) = 1 := by
  rw [U_apply, LinearEquiv.apply_symm_apply, intCoord_stdBasisVec, intCoord_stdBasisVec]
  simp

theorem ux_surjective (θ : B) (x : PrimeSpectrum B) : Function.Surjective (ux p θ x) := by
  intro m
  induction m using LocalizedModule.induction_on with
  | h t s =>
    refine ⟨Localization.mk t s • ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (ω p).symm (stdBasisVec ℚ_[p] 0)), ?_⟩
    rw [map_smul, ux_tmul, U_e0, one_smul, LocalizedModule.mk_smul_mk, smul_eq_mul, mul_one, mul_one]

theorem mem_of_mk_mem_smul_top (x : PrimeSpectrum B) (t : B)
    (h : LocalizedModule.mk t (1 : x.asIdeal.primeCompl) ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x B))) :
    t ∈ x.asIdeal := by

  have key : ∀ m : stalk B x B, m ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x B)) →
      ∃ s : B, s ∉ x.asIdeal ∧ ∃ q ∈ x.asIdeal, s • m = LocalizedModule.mk q 1 := by
    intro m hm
    induction hm using Submodule.smul_induction_on' with
    | smul r hr n _ =>
      induction n using LocalizedModule.induction_on with
      | h q s =>
        refine ⟨s, s.2, r * q, x.asIdeal.mul_mem_right _ hr, ?_⟩
        rw [smul_comm, LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel, LocalizedModule.smul'_mk,
          smul_eq_mul]
    | add y _ z _ hy hz =>
      obtain ⟨s, hs, q, hq, hsq⟩ := hy
      obtain ⟨s', hs', q', hq', hsq'⟩ := hz
      refine ⟨s * s', fun hh => (x.isPrime.mem_or_mem hh).elim hs hs', s' * q + s * q',
        x.asIdeal.add_mem (x.asIdeal.mul_mem_left _ hq) (x.asIdeal.mul_mem_left _ hq'), ?_⟩
      rw [smul_add, show (s * s') • y = s' • (s • y) by rw [mul_comm, mul_smul], show (s * s') • z = s • (s' • z) by
        rw [mul_smul], hsq, hsq', LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, smul_eq_mul, smul_eq_mul]
      exact (map_add (LocalizedModule.mkLinearMap x.asIdeal.primeCompl B) _ _).symm
  obtain ⟨s, hs, q, hq, hsq⟩ := key _ h
  rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at hsq
  obtain ⟨c, hc⟩ := hsq
  simp only [one_smul, Submonoid.smul_def, smul_eq_mul] at hc

  have : ↑c * s * t ∈ x.asIdeal := by rw [mul_assoc, hc]; exact x.asIdeal.mul_mem_left _ hq
  rcases x.isPrime.mem_or_mem this with h1 | h1
  · exact ((x.isPrime.mem_or_mem h1).elim (fun h2 => (c.2 h2).elim) (fun h2 => (hs h2).elim))
  · exact h1

end B25NE

namespace B25NE

open B25N3

variable (p : ℕ) [Fact p.Prime]

theorem exists_pow_ne (k : Type) [Field k] [IsAlgClosed k] : ∃ l : k, l ^ p ≠ l := by
  by_contra hall
  push_neg at hall
  apply FiniteField.X_pow_card_sub_X_ne_zero k (Fact.out : p.Prime).one_lt
  apply Polynomial.eq_zero_of_infinite_isRoot
  have : {x : k | Polynomial.IsRoot (Polynomial.X ^ p - Polynomial.X) x} = Set.univ := by
    ext l; simp [Polynomial.IsRoot, sub_eq_zero, hall l]
  rw [this]; exact Set.infinite_univ

theorem isUnit_teichmuller_pow_sub (k : Type) [Field k] [CharP k p] (l : k) (hl : l ^ p ≠ l) :
    IsUnit (WittVector.teichmuller p l ^ p - WittVector.teichmuller p l) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [← WittVector.constantCoeff_apply, map_sub, map_pow, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero]
  exact sub_ne_zero.mpr hl

variable {B : Type} [CommRing B] [Algebra ℤ_[p] B] (θ : B)

theorem inclBaseChange_self (x : PrimeSpectrum B) (w : latticeBaseChange ℤ_[p] ℚ_[p] (locRing B x) (Lodd p)) :
    inclBaseChange (locRing B x) (M' := Lodd p) (M := Lodd p) le_rfl w = w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add a b ha hb => rw [map_add, ha, hb]
  | tmul b v => unfold inclBaseChange; rw [LinearMap.baseChange_tmul]; rfl

theorem smulInto_baseChange_tmul (x : PrimeSpectrum B)
    (h : ∀ v ∈ (Lodd p).1, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ (Lodd p).1) (b : locRing B x) (v : ↥(Lodd p).1) :
    (smulInto (p : ℤ_[p]) h).baseChange (locRing B x) (b ⊗ₜ[ℤ_[p]] v) = b ⊗ₜ[ℤ_[p]] ((p : ℤ_[p]) • v) := by
  rw [LinearMap.baseChange_tmul]
  congr 1 <;> exact Subtype.ext (by rw [coe_smulInto_apply, Submodule.coe_smul, algebraMap_smul])

theorem map_smul_id {M : Type} [AddCommGroup M] [Module B M] (x : PrimeSpectrum B) (c : B)
    (m : LocalizedModule x.asIdeal.primeCompl M) :
    LocalizedModule.map x.asIdeal.primeCompl (c • (LinearMap.id : M →ₗ[B] M)) m = c • m := by
  rw [LinearMap.map_smul, LocalizedModule.map_id]; rfl

theorem ux_smulInto (x : PrimeSpectrum B)
    (h : ∀ v ∈ (Lodd p).1, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ (Lodd p).1)
    (w : latticeBaseChange ℤ_[p] ℚ_[p] (locRing B x) (Lodd p)) :
    ux p θ x ((smulInto (p : ℤ_[p]) h).baseChange (locRing B x) w) =
      LocalizedModule.map x.asIdeal.primeCompl (algebraMap ℤ_[p] B (p : ℤ_[p]) • (LinearMap.id : B →ₗ[B] B))
        (ux p θ x w) := by
  rw [map_smul_id]
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, smul_add, ha, hb]
  | tmul b v =>
    rw [smulInto_baseChange_tmul, ux_tmul, ux_tmul, map_smul,
      show ((p : ℤ_[p]) • U p θ v) = algebraMap ℤ_[p] B (p : ℤ_[p]) • U p θ v from (algebraMap_smul B (p : ℤ_[p]) _).symm,
      ← LocalizedModule.smul'_mk, smul_comm]

noncomputable def datum (hθ : IsUnit (θ ^ p - θ)) (hB : IsNilpotent (p : B)) :
    DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B where
  N₀ _ := (Lodd p).1
  N₁ _ := (Lodd p).1
  full₀ _ := (Lodd p).2
  full₁ _ := (Lodd p).2
  le _ := le_rfl
  smul_le _ v hv := by rw [algebraMap_smul]; exact (Lodd p).1.smul_mem _ hv
  isOpen_setOf_mem₀ v := by by_cases h : v ∈ (Lodd p).1 <;> simp [h]
  isOpen_setOf_mem₁ v := by by_cases h : v ∈ (Lodd p).1 <;> simp [h]
  T₀ := B
  T₁ := B
  invertible₀ := inferInstance
  invertible₁ := inferInstance
  Pi₀ := LinearMap.id
  Pi₁ := algebraMap ℤ_[p] B (p : ℤ_[p]) • LinearMap.id
  Pi₁_Pi₀ _ := rfl
  Pi₀_Pi₁ _ := rfl
  u₀ x := ux p θ x
  u₁ x := ux p θ x
  u₁_incl x w := by
    rw [LocalizedModule.map_id]
    exact congrArg _ (inclBaseChange_self p x w)
  u₀_smul x w := ux_smulInto p θ x _ w
  u₀_surjective x := ux_surjective p θ x
  u₁_surjective x := ux_surjective p θ x
  u₀_continuous x v hv := ⟨1, U p θ ⟨v, hv⟩, fun h1 => x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1),
    fun y hy => ⟨hv, by rw [ux_tmul, one_smul]; rfl⟩⟩
  u₁_continuous x v hv := ⟨1, U p θ ⟨v, hv⟩, fun h1 => x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1),
    fun y hy => ⟨hv, by rw [ux_tmul, one_smul]; rfl⟩⟩
  locallyConstant₀ x _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ _ _ => rfl⟩
  locallyConstant₁ x _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ _ _ => rfl⟩
  injective₀ x v hv := by
    have hpx : algebraMap ℤ_[p] B (p : ℤ_[p]) ∈ x.asIdeal := by
      obtain ⟨n, hn⟩ := hB
      rw [map_natCast]
      exact x.isPrime.mem_of_pow_mem n (hn ▸ x.asIdeal.zero_mem)
    apply exists_of_U_mem p θ hθ x hpx v
    apply mem_of_mk_mem_smul_top x
    have e : ux p θ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] v) = LocalizedModule.mk (U p θ v) 1 := by rw [ux_tmul, one_smul]
    rw [← e]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    rw [← hab]
    refine Submodule.add_mem _ ?_ hb
    obtain ⟨m', hm'⟩ := ha
    rw [← hm', map_smul_id]
    exact Submodule.smul_mem_smul hpx Submodule.mem_top
  injective₁ x v _ := v.2
  hasDetIndex₀ x hx := by
    exfalso
    apply x.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : B) ∈ x.asIdeal • (⊤ : Submodule B B) := hx ⟨1, rfl⟩
    exact (Submodule.smul_le.mpr fun r hr b _ => x.asIdeal.mul_mem_right b hr) this
  hasDetIndex₁ x _ := hasDetIndex_Lodd p

end B25NE

open B25NE in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (B : Type) [CommRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) :
    Nonempty (DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) := by
  obtain ⟨l, hl⟩ := exists_pow_ne p k
  have hθ : IsUnit ((ψ (WittVector.teichmuller p l)) ^ p - ψ (WittVector.teichmuller p l)) := by
    rw [← map_pow, ← map_sub]; exact (isUnit_teichmuller_pow_sub p k l hl).map ψ
  exact ⟨datum p _ hθ hB⟩

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_nonempty_of_isNilpotent_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_nonempty_of_isNilpotent_of_isAlgClosed (solution)
