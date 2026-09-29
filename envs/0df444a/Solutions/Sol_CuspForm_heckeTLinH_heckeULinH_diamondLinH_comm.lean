-- Prove2me | solution 1 for CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1ccb2e57-c5e2-51ca-9839-9d18215f45c0

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Mathlib.LinearAlgebra.Basis.Basic
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open scoped MatrixGroups ModularForm
open ModularFormClass

namespace COMMALL

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)

abbrev W : Type := CuspForm (CohCarrier.GammaH M H) k

structure Datum where
  n : ℕ
  L : Fin n → ℕ
  hL : ∀ i, L i ∣ M
  ε : (i : Fin n) → DirichletCharacter ℂ (L i)
  g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k
  G : Fin n → ℕ → W M H k
  hli : LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ))
  hspan : Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤
  hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    CuspForm.heckeTLinH k hℓ hℓM (G i d) = qCoeff (g i) ℓ • G i d
  hD : ∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
    CuspForm.diamondLinH k u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d
  hU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
    (q ∣ d → CuspForm.heckeULinH k q (G i d) = G i (d / q)) ∧
    (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH k q (G i d) = qCoeff (g i) q • G i d) ∧
    (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH k q (G i d) =
      qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ (k - 1)) • G i (d * q))

theorem nonempty_datum : Nonempty (Datum M H k) := by
  obtain ⟨n, L, hL, ε, g, G, -, -, -, -, hli, hspan, hT, hD, hU⟩ :=
    CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply M H k
  exact ⟨⟨n, L, hL, ε, g, G, hli, hspan, hT, hD, hU⟩⟩

variable {M H k}
variable (𝒟 : Datum M H k)

abbrev Idx : Type := Σ i : Fin 𝒟.n, ↥(Nat.divisors (M / 𝒟.L i))

def basis : Module.Basis (Idx 𝒟) ℂ (W M H k) :=
  Module.Basis.mk (v := fun x : Idx 𝒟 => 𝒟.G x.1 (x.2 : ℕ)) 𝒟.hli (by rw [𝒟.hspan])

theorem basis_apply (x : Idx 𝒟) : basis 𝒟 x = 𝒟.G x.1 (x.2 : ℕ) := by simp [basis]

def V (i : Fin 𝒟.n) : Submodule ℂ (W M H k) :=
  Submodule.span ℂ (Set.range fun d : ↥(Nat.divisors (M / 𝒟.L i)) => 𝒟.G i (d : ℕ))

theorem L_ne_zero (i : Fin 𝒟.n) : 𝒟.L i ≠ 0 := fun h => by
  have := 𝒟.hL i; rw [h, zero_dvd_iff] at this; exact NeZero.ne M this

theorem div_ne_zero (i : Fin 𝒟.n) : M / 𝒟.L i ≠ 0 :=
  Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (𝒟.hL i))
    (Nat.pos_of_ne_zero (L_ne_zero 𝒟 i)))

theorem G_mem_V (i : Fin 𝒟.n) {d : ℕ} (hd : d ∣ M / 𝒟.L i) : 𝒟.G i d ∈ V 𝒟 i :=
  Submodule.subset_span ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, div_ne_zero 𝒟 i⟩⟩, rfl⟩

theorem scalar_on_V (T : Module.End ℂ (W M H k)) (i : Fin 𝒟.n) (c : ℂ)
    (h : ∀ d : ℕ, d ∣ M / 𝒟.L i → T (𝒟.G i d) = c • 𝒟.G i d) : ∀ v ∈ V 𝒟 i, T v = c • v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨d, rfl⟩ := hx; exact h d (Nat.dvd_of_mem_divisors d.2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem stab_on_V (T : Module.End ℂ (W M H k)) (i : Fin 𝒟.n)
    (h : ∀ d : ℕ, d ∣ M / 𝒟.L i → T (𝒟.G i d) ∈ V 𝒟 i) : ∀ v ∈ V 𝒟 i, T v ∈ V 𝒟 i := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨d, rfl⟩ := hx; exact h d (Nat.dvd_of_mem_divisors d.2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem heckeT_scalar {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin 𝒟.n) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∀ v ∈ V 𝒟 i, CuspForm.heckeTLinH k hℓ hℓM v = qCoeff (𝒟.g i) ℓ • v :=
  scalar_on_V 𝒟 _ i _ (fun d hd => 𝒟.hT ℓ hℓ hℓM i d hd)

theorem diamond_scalar (u : (ZMod M)ˣ) (i : Fin 𝒟.n) :
    ∀ v ∈ V 𝒟 i, CuspForm.diamondLinH k u v = DirichletCharacter.changeLevel (𝒟.hL i) (𝒟.ε i) (u : ZMod M) • v :=
  scalar_on_V 𝒟 _ i _ (fun d hd => 𝒟.hD u i d hd)

theorem mul_dvd_div {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (i : Fin 𝒟.n) (hqL : ¬ q ∣ 𝒟.L i) {d : ℕ}
    (hd : d ∣ M / 𝒟.L i) (hqd : ¬ q ∣ d) : d * q ∣ M / 𝒟.L i := by
  have hcop : Nat.Coprime d q := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
  refine hcop.mul_dvd_of_dvd_of_dvd hd ?_
  have hqML : Nat.Coprime q (𝒟.L i) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqL
  have : q ∣ 𝒟.L i * (M / 𝒟.L i) := by rw [Nat.mul_div_cancel' (𝒟.hL i)]; exact hqM
  exact hqML.dvd_of_dvd_mul_left this

theorem heckeU_stab {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (i : Fin 𝒟.n) :
    ∀ v ∈ V 𝒟 i, CuspForm.heckeULinH k q v ∈ V 𝒟 i := by
  refine stab_on_V 𝒟 _ i (fun d hd => ?_)
  obtain ⟨h1, h2, h3⟩ := 𝒟.hU q hq hqM i d hd
  by_cases hqd : q ∣ d
  · rw [h1 hqd]; exact G_mem_V 𝒟 i ((Nat.div_dvd_of_dvd hqd).trans hd)
  · by_cases hqL : q ∣ 𝒟.L i
    · rw [h2 hqd hqL]; exact Submodule.smul_mem _ _ (G_mem_V 𝒟 i hd)
    · rw [h3 hqd hqL]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (G_mem_V 𝒟 i hd))
        (Submodule.smul_mem _ _ (G_mem_V 𝒟 i (mul_dvd_div 𝒟 hq hqM i hqL hd hqd)))

theorem comm_of_scalar_of_stab (A B : Module.End ℂ (W M H k)) (c : Fin 𝒟.n → ℂ)
    (hA : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, A v = c i • v) (hB : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, B v ∈ V 𝒟 i) :
    ∀ f : W M H k, A (B f) = B (A f) := by
  have : A * B = B * A := by
    refine (basis 𝒟).ext fun x => ?_
    obtain ⟨i, d⟩ := x
    have hmem : 𝒟.G i d ∈ V 𝒟 i := G_mem_V 𝒟 i (Nat.dvd_of_mem_divisors d.2)
    rw [basis_apply, Module.End.mul_apply, Module.End.mul_apply, hA i _ (hB i _ hmem), hA i _ hmem, map_smul]
  intro f
  exact congrArg (fun T : Module.End ℂ (W M H k) => T f) this

theorem stab_of_scalar (A : Module.End ℂ (W M H k)) (c : Fin 𝒟.n → ℂ)
    (hA : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, A v = c i • v) : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, A v ∈ V 𝒟 i :=
  fun i v hv => by rw [hA i v hv]; exact Submodule.smul_mem _ _ hv

end COMMALL

end

open COMMALL in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓ' : ℓ'.Prime) (hℓ'M : ¬ ℓ' ∣ M)
        (f : CuspForm (CohCarrier.GammaH M H) k),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.heckeTLinH k hℓ' hℓ'M f) =
        CuspForm.heckeTLinH k hℓ' hℓ'M (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (q : ℕ), q.Prime → q ∣ M →
        ∀ f : CuspForm (CohCarrier.GammaH M H) k,
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.heckeULinH k q f) =
        CuspForm.heckeULinH k q (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.diamondLinH k d f) =
        CuspForm.diamondLinH k d (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      CuspForm.heckeULinH k q (CuspForm.diamondLinH k d f) =
        CuspForm.diamondLinH k d (CuspForm.heckeULinH k q f)) ∧
    (∀ (d d' : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      CuspForm.diamondLinH k d (CuspForm.diamondLinH k d' f) =
        CuspForm.diamondLinH k d' (CuspForm.diamondLinH k d f)) := by
  obtain ⟨𝒟⟩ := nonempty_datum M H k
  refine ⟨fun ℓ ℓ' hℓ hℓM hℓ' hℓ'M f => ?_, fun ℓ hℓ hℓM q hq hqM f => ?_, fun ℓ hℓ hℓM d f => ?_,
    fun q hq hqM d f => ?_, fun d d' f => ?_⟩
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
    exact comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => heckeT_scalar 𝒟 hℓ hℓM i)
      (stab_of_scalar 𝒟 _ _ (fun i => heckeT_scalar 𝒟 hℓ' hℓ'M i)) f
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => heckeT_scalar 𝒟 hℓ hℓM i) (fun i => heckeU_stab 𝒟 hq hqM i) f
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => heckeT_scalar 𝒟 hℓ hℓM i)
      (stab_of_scalar 𝒟 _ _ (fun i => diamond_scalar 𝒟 d i)) f
  · exact (comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => diamond_scalar 𝒟 d i) (fun i => heckeU_stab 𝒟 hq hqM i) f).symm
  · exact comm_of_scalar_of_stab 𝒟 _ _ _ (fun i => diamond_scalar 𝒟 d i)
      (stab_of_scalar 𝒟 _ _ (fun i => diamond_scalar 𝒟 d' i)) f

end S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
end P2MW
export P2MW.S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm (solution)
