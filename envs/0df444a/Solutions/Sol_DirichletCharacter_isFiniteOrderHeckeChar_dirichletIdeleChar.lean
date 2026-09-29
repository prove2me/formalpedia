-- Prove2me | solution 1 for DirichletCharacter.isFiniteOrderHeckeChar_dirichletIdeleChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8d0e4e3d-4d73-5c45-ad45-6d6c723808f9

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Rat.HeightOneSpectrum NumberField.AdelicLevel RatIdele
open scoped Topology

namespace P124

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

attribute [local instance] RatIdele.fact_prime_of_mem_primeFactors

theorem finite_setOf_natGenerator_dvd (N : ℕ) [NeZero N] :
    {v : HeightOneSpectrum (𝓞 ℚ) | natGenerator v ∣ N}.Finite := by
  refine Set.Finite.of_finite_image (f := fun v => natGenerator v) ?_ fun v _ w _ h => eq_of_natGenerator_eq h
  refine (N.divisors.finite_toSet).subset ?_
  rintro _ ⟨v, hv, rfl⟩
  exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨hv, NeZero.ne N⟩)

def finCongr (N : ℕ) : Set 𝔸ℚf :=
  {y | y ∈ integralFiniteAdeles (𝓞 ℚ) ℚ ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ), natGenerator v ∣ N →
    Valued.v (y v - 1) ≤ Valued.v (((N : ℕ) : v.adicCompletion ℚ))}

theorem isOpen_finCongr (N : ℕ) [NeZero N] : IsOpen (finCongr N) := by
  have h : finCongr N = integralFiniteAdeles (𝓞 ℚ) ℚ ∩
      ⋂ v ∈ {v : HeightOneSpectrum (𝓞 ℚ) | natGenerator v ∣ N},
        (fun y : 𝔸ℚf => finAdeleEval (𝓞 ℚ) ℚ v y - 1) ⁻¹'
          {z | Valued.v z ≤ Valued.v (((N : ℕ) : v.adicCompletion ℚ))} := by
    ext y
    simp only [finCongr, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      finAdeleEval_apply]
  rw [h]
  exact (isOpen_integralFiniteAdeles _ _).inter ((finite_setOf_natGenerator_dvd N).isOpen_biInter
    fun v _ => (isOpen_setOf_valued_le v _ (natCast_adicCompletion_ne_zero v (NeZero.ne N))).preimage
      ((continuous_finAdeleEval (𝓞 ℚ) ℚ v).sub continuous_const))

theorem continuous_archCoord : Continuous (archCoord : (𝔸ℚ)ˣ → ℝ) := by
  unfold archCoord
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
    ((continuous_archEval ℚ Rat.infinitePlace).comp
      ((continuous_adeleArch (𝓞 ℚ) ℚ).comp Units.continuous_val))

def congrNhd (N : ℕ) : Set (𝔸ℚ)ˣ :=
  {x | (x : 𝔸ℚ).2 ∈ finCongr N ∧ ((x⁻¹ : (𝔸ℚ)ˣ) : 𝔸ℚ).2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ ∧ 0 < archCoord x}

theorem isOpen_congrNhd (N : ℕ) [NeZero N] : IsOpen (congrNhd N) := by
  refine ((isOpen_finCongr N).preimage ((continuous_adeleFin (𝓞 ℚ) ℚ).comp Units.continuous_val)).inter
    (((isOpen_integralFiniteAdeles (𝓞 ℚ) ℚ).preimage
      ((continuous_adeleFin (𝓞 ℚ) ℚ).comp Units.continuous_coe_inv)).inter
        (isOpen_lt continuous_const continuous_archCoord))

theorem one_mem_congrNhd (N : ℕ) : (1 : (𝔸ℚ)ˣ) ∈ congrNhd N := by
  refine ⟨⟨fun v => one_mem _, fun v _ => ?_⟩, fun v => ?_, by rw [archCoord_one]; exact one_pos⟩
  · rw [show ((((1 : (𝔸ℚ)ˣ) : 𝔸ℚ).2) : 𝔸ℚf) v = 1 from rfl, sub_self, map_zero]
    exact zero_le'
  · rw [inv_one]
    exact one_mem _

theorem congrNhd_mem_nhds_one (N : ℕ) [NeZero N] : congrNhd N ∈ 𝓝 (1 : (𝔸ℚ)ˣ) :=
  (isOpen_congrNhd N).mem_nhds (one_mem_congrNhd N)

variable {N : ℕ} {x : (𝔸ℚ)ˣ}

theorem valued_snd_eq_one (hx : x ∈ congrNhd N) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((x : 𝔸ℚ).2 v) = 1 := by
  rw [valued_snd_eq, ordAt_eq_zero_of_le_one ((mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (hx.1.1 v))
    ((mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (hx.2.1 v))]
  rfl

theorem ρ_eq_one (hx : x ∈ congrNhd N) : ρ x = 1 :=
  ρ_eq_of_isNormalizer ⟨fun v => by rw [valued_snd_eq_one hx v, map_one],
    by rw [Rat.cast_one, mul_one]; exact hx.2.2⟩

theorem unitAt_eq (hx : x ∈ congrNhd N) (v : HeightOneSpectrum (𝓞 ℚ)) : unitAt v x = (x : 𝔸ℚ).2 v := by
  unfold unitAt
  rw [ρ_eq_one hx, map_one, inv_one, mul_one]

theorem valued_natCast_eq_valued_pow (N : ℕ) [NeZero N] (p : ℕ) [hp : Fact p.Prime] :
    Valued.v (((N : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩).adicCompletion ℚ))
      = Valued.v ((((p : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩).adicCompletion ℚ)) ^ N.factorization p) := by
  set v := (primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩ with hv
  have hgen : natGenerator v = p := natGenerator_primesEquiv_symm ⟨p, hp.out⟩
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N p]
  rw [Nat.cast_mul, map_mul, Nat.cast_pow]
  have hm : Valued.v (((N / p ^ N.factorization p : ℕ) : v.adicCompletion ℚ)) = 1 := by
    rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat]
    refine valuation_natCast_of_not_dvd v ?_
    rw [hgen]
    exact Nat.not_dvd_ordCompl hp.out (NeZero.ne N)
  rw [hm, mul_one]

set_option maxHeartbeats 3200000 in

theorem toZModPow_unitPadicAt_eq_one {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hρ : ρ x = 1)
    (hv : Valued.v ((x : 𝔸ℚ).2 ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) - 1)
      ≤ Valued.v ((((p : ℕ) : ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩).adicCompletion ℚ)) ^ k)) :
    PadicInt.toZModPow k (unitPadicAt p x) = 1 := by
  set v := (primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩ with hvdef
  set e := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, hp.out⟩).symm.toAlgEquiv.toRingEquiv with he
  have hp0 : ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := natCast_adicCompletion_ne_zero v hp.out.ne_zero
  have hpk0 : ((p : ℕ) : v.adicCompletion ℚ) ^ k ≠ 0 := pow_ne_zero _ hp0

  have hw : ((x : 𝔸ℚ).2 v - 1) * (((p : ℕ) : v.adicCompletion ℚ) ^ k)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [mem_adicCompletionIntegers, map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ hv zero_le'
  set w : v.adicCompletionIntegers ℚ := ⟨_, hw⟩ with hwdef
  have hunit : unitIntAt v x - 1 = ((p : ℕ) : v.adicCompletionIntegers ℚ) ^ k * w := by
    apply Subtype.ext
    show unitAt v x - 1 = (((p : ℕ) : v.adicCompletion ℚ)) ^ k * (((x : 𝔸ℚ).2 v - 1) * (((p : ℕ) : v.adicCompletion ℚ) ^ k)⁻¹)
    rw [mul_comm, inv_mul_cancel_right₀ hpk0]
    unfold unitAt
    rw [hρ, map_one, inv_one, mul_one]
  have hker : unitPadicAt p x - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := p) k) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton']
    refine ⟨e w, ?_⟩
    show e w * (p : ℤ_[p]) ^ k = e (unitIntAt v x) - 1
    rw [← map_one e, ← map_sub, hunit, map_mul, map_pow, map_natCast, mul_comm]
  rwa [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hker

theorem unitResidue_eq_one_of_mem_congrNhd [NeZero N] (hx : x ∈ congrNhd N) : unitResidue N x = 1 := by
  apply (ZMod.equivPi N (NeZero.ne N)).injective
  rw [equivPi_unitResidue, map_one]
  funext p
  show PadicInt.toZModPow (N.factorization p) (unitPadicAt p x) = 1
  have hdvd : natGenerator ((primesEquiv (R := 𝓞 ℚ)).symm ⟨p, (fact_prime_of_mem_primeFactors p).out⟩) ∣ N := by
    rw [natGenerator_primesEquiv_symm]
    exact Nat.dvd_of_mem_primeFactors p.2
  refine toZModPow_unitPadicAt_eq_one (ρ_eq_one hx) ?_
  rw [← valued_natCast_eq_valued_pow N p]
  exact hx.1.2 _ hdvd

theorem valued_natCast_eq_exp_neg_idealMultiplicity (N : ℕ) [NeZero N] (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((N : ℕ) : v.adicCompletion ℚ))
      = exp (-(HeckeCharacter.idealMultiplicity ℚ v (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) : ℤ)) := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), valued_algebraMap_rat,
    show ((N : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((N : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) N).symm,
    valuation_of_algebraMap, intValuation_if_neg v (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  rfl

theorem mem_congrNhd_of_modulus {N : ℕ} [NeZero N] {u : (𝔸ℚ)ˣ} (hu : (u : 𝔸ℚ).1 = 1)
    (hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : 𝔸ℚ).2 v) = 1 ∧
      Valued.v ((u : 𝔸ℚ).2 v - 1)
        ≤ exp (-(HeckeCharacter.idealMultiplicity ℚ v (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) : ℤ))) :
    u ∈ congrNhd N := by
  refine ⟨⟨fun v => (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (hv v).1.le, fun v _ => ?_⟩, fun v => ?_, ?_⟩
  · rw [valued_natCast_eq_exp_neg_idealMultiplicity]
    exact (hv v).2
  · rw [mem_adicCompletionIntegers]
    have h := valued_snd_inv_mul u v
    rw [(hv v).1, mul_one] at h
    exact h.le
  · unfold archCoord
    rw [hu, show (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 1 from rfl, map_one]
    exact one_pos

section Thm

variable [NeZero N] (χ : DirichletCharacter ℂ N)

theorem congrNhd_subset_ker_dirichletIdeleChar :
    congrNhd N ⊆ ((DirichletCharacter.dirichletIdeleChar χ).ker : Set (𝔸ℚ)ˣ) := fun _ hx =>
  (DirichletCharacter.dirichletIdeleChar χ).mem_ker.mpr (DirichletCharacter.dirichletIdeleChar_eq_one_of_unitResidue_eq_one χ
    (unitResidue_eq_one_of_mem_congrNhd hx))

theorem ker_dirichletIdeleChar_mem_nhds_one : ((DirichletCharacter.dirichletIdeleChar χ).ker : Set (𝔸ℚ)ˣ) ∈ 𝓝 (1 : (𝔸ℚ)ˣ) :=
  Filter.mem_of_superset (congrNhd_mem_nhds_one N) (congrNhd_subset_ker_dirichletIdeleChar χ)

theorem isOpen_ker_dirichletIdeleChar : IsOpen ((DirichletCharacter.dirichletIdeleChar χ).ker : Set (𝔸ℚ)ˣ) :=
  Subgroup.isOpen_of_mem_nhds _ (ker_dirichletIdeleChar_mem_nhds_one χ)

theorem continuous_dirichletIdeleChar : Continuous (DirichletCharacter.dirichletIdeleChar χ) := by
  refine continuous_of_continuousAt_one (DirichletCharacter.dirichletIdeleChar χ) ?_
  rw [ContinuousAt, map_one]
  intro s hs
  refine Filter.mem_map.mpr (Filter.mem_of_superset (ker_dirichletIdeleChar_mem_nhds_one χ) fun x hx => ?_)
  rw [Set.mem_preimage, (DirichletCharacter.dirichletIdeleChar χ).mem_ker.mp hx]
  exact mem_of_mem_nhds hs

theorem dirichletIdeleChar_pow_card_eq_one : (DirichletCharacter.dirichletIdeleChar χ) ^ Fintype.card (ZMod N)ˣ = 1 := by
  ext x : 1
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, DirichletCharacter.dirichletIdeleChar, MonoidHom.inv_apply, inv_pow,
    MonoidHom.comp_apply, ← map_pow, pow_card_eq_one, map_one, inv_one]

theorem isOfFinOrder_dirichletIdeleChar : IsOfFinOrder (DirichletCharacter.dirichletIdeleChar χ) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, dirichletIdeleChar_pow_card_eq_one χ⟩

theorem isFiniteOrderHeckeChar_dirichletIdeleChar_port :
    HeckeCharacter.IsFiniteOrderHeckeChar ℚ (DirichletCharacter.dirichletIdeleChar χ) :=
  ⟨fun q => DirichletCharacter.dirichletIdeleChar_principal χ q, continuous_dirichletIdeleChar χ, isOfFinOrder_dirichletIdeleChar χ⟩

theorem admitsModulus_dirichletIdeleChar_port :
    HeckeCharacter.AdmitsModulus ℚ (DirichletCharacter.dirichletIdeleChar χ) (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) := fun _ hu hv =>
  DirichletCharacter.dirichletIdeleChar_eq_one_of_unitResidue_eq_one χ (unitResidue_eq_one_of_mem_congrNhd (mem_congrNhd_of_modulus hu hv))

end Thm

end P124

end

open NumberField IsDedekindDomain

theorem solution {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : HeckeCharacter.IsFiniteOrderHeckeChar ℚ χ.dirichletIdeleChar :=
  P124.isFiniteOrderHeckeChar_dirichletIdeleChar_port χ

end S_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar
end P2MW
export P2MW.S_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar (solution)
