-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/eae998ef-547a-5f4f-ad64-68a5f60eee51

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_div_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMer_eq_mk_of_isThetaPair
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_setOf_dist_le
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_BruhatTits_exists_pos_forall_isOfFinOrder_pow_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_quotVert_prod_equiv_and_quotEdge_equiv_oriented_of_exchanger
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_quotVert_equiv_quotEdge_equiv_of_iso_of_smul_eq
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one.CerednikDrinfeld CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.PseudoUniformizer Omega.IsExhausted Omega.holRing Omega.coe_smul_upperHalfPlane Omega.HolRingOf Omega.HolRingOf.isDomain_iff Omega.merField Omega.upperHalfPlane Omega.theta Mumford.fracAct Mumford.fracAct_algebraMap Mumford.frac_smul_def Mumford.invariantFieldOf Mumford.mem_invariantFieldOf_iff Mumford.vertexType Mumford.typePreserving Mumford.mem_typePreserving_iff tree BruhatTits.tree Mumford.GraphAction Mumford.QuotEdge Mumford.QuotVert Mumford.ActsThrough Omega.IsThetaPair Omega.thetaMer Omega.IsDiscrete Omega.exists_holRing_div_eq_theta Omega.exists_monoidHom_fracAct_thetaMer_eq Omega.thetaMer_eq_mk_of_isThetaPair Omega.isDiscrete_of_finite_stabilizer_stdVertex BruhatTits.finite_setOf_dist_le BruhatTits.tree_connected_and_colorable_two BruhatTits.exists_pos_forall_isOfFinOrder_pow_eq_one Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter"
namespace BruhatTits
p2m_export "CerednikDrinfeld.BruhatTits" "tree finite_setOf_dist_le tree_connected_and_colorable_two exists_pos_forall_isOfFinOrder_pow_eq_one"
namespace StabExp
p2m_open "CerednikDrinfeld.BruhatTits CerednikDrinfeld"

open MulAction LT.LatticeTree

variable {R₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
  {K₀ : Type} [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

theorem exists_adj (w : Vertex R₀ K₀) : ∃ x : Vertex R₀ K₀, (tree R₀ K₀).Adj w x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  have hconn := (CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀).1

  have hns := not_subsingleton_fixedVertexSet_scalarGL (R := R₀) (K := K₀) hϖ 1
  rw [fixedVertexSet_scalarGL, Set.subsingleton_univ_iff, not_subsingleton_iff_nontrivial] at hns
  obtain ⟨w', hw'⟩ := exists_ne w
  obtain ⟨p⟩ := hconn.preconnected w w'
  cases p with
  | nil => exact absurd rfl hw'.symm
  | cons h _ => exact ⟨_, h⟩

theorem finite_setOf_dart_fst_eq [Finite (IsLocalRing.ResidueField R₀)] (w : Vertex R₀ K₀) :
    {d : (tree R₀ K₀).Dart | d.fst = w}.Finite := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  haveI : Finite (R₀ ⧸ IsLocalRing.maximalIdeal R₀) := ‹Finite (IsLocalRing.ResidueField R₀)›
  haveI : Finite (R₀ ⧸ Ideal.span {ϖ}) :=
    Finite.of_equiv (R₀ ⧸ IsLocalRing.maximalIdeal R₀) (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).toEquiv
  have hball := CerednikDrinfeld.BruhatTits.finite_setOf_dist_le R₀ K₀ ϖ hϖ w 1
  refine Set.Finite.of_injOn (f := fun d : (tree R₀ K₀).Dart => d.snd) (fun d hd => ?_) (fun d₁ hd₁ d₂ hd₂ h => ?_) hball
  ·
    show (tree R₀ K₀).dist w d.snd ≤ 1
    rw [Set.mem_setOf_eq] at hd
    rw [← hd, SimpleGraph.dist_eq_one_iff_adj.2 d.adj]
  · rw [Set.mem_setOf_eq] at hd₁ hd₂
    exact SimpleGraph.Dart.ext _ _ (Prod.ext (hd₁.trans hd₂.symm) h)

theorem finite_stabilizer_vertex [Finite (IsLocalRing.ResidueField R₀)] (Δ : Subgroup PGL(2, K₀))
    (hfin : ∀ d : (tree R₀ K₀).Dart, Finite (stabilizer ↥Δ d)) (w : Vertex R₀ K₀) :
    Finite (stabilizer ↥Δ w) := by
  obtain ⟨x, hx⟩ := exists_adj w
  let d₀ : (tree R₀ K₀).Dart := ⟨(w, x), hx⟩
  let S : Subgroup ↥Δ := stabilizer ↥Δ w

  haveI hH : Finite (stabilizer ↥S d₀) := by
    haveI := hfin d₀
    refine Finite.of_injective (fun h : stabilizer ↥S d₀ => (⟨((h : ↥S) : ↥Δ), ?_⟩ : stabilizer ↥Δ d₀)) ?_
    · have := h.2
      rw [mem_stabilizer_iff] at this ⊢
      exact this
    · intro a b hab
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun z : stabilizer ↥Δ d₀ => (z : ↥Δ)) hab

  haveI hQ : Finite (↥S ⧸ stabilizer ↥S d₀) := by
    have horb : (orbit ↥S d₀).Finite := by
      refine (finite_setOf_dart_fst_eq w).subset ?_
      rintro d ⟨s, rfl⟩
      show ((s : ↥Δ) • d₀).fst = w
      have hs := s.2
      rw [mem_stabilizer_iff] at hs
      exact hs
    haveI := horb.to_subtype
    exact Finite.of_equiv _ (orbitEquivQuotientStabilizer ↥S d₀)
  apply Nat.finite_of_card_ne_zero
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (stabilizer ↥S d₀)]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

omit [IsDomain R₀] [IsDiscreteValuationRing R₀] [IsFractionRing R₀ K₀] in

theorem natCard_stabilizer_smul (Δ : Subgroup PGL(2, K₀)) (g : ↥Δ) (w : Vertex R₀ K₀) :
    Nat.card (stabilizer ↥Δ (g • w)) = Nat.card (stabilizer ↥Δ w) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end CerednikDrinfeld.BruhatTits.StabExp

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Omega.PseudoUniformizer Omega.IsExhausted Omega.holRing Omega.coe_smul_upperHalfPlane Omega.HolRingOf Omega.HolRingOf.isDomain_iff Omega.merField Omega.upperHalfPlane Omega.theta Mumford.fracAct Mumford.fracAct_algebraMap Mumford.frac_smul_def Mumford.invariantFieldOf Mumford.mem_invariantFieldOf_iff Mumford.vertexType Mumford.typePreserving Mumford.mem_typePreserving_iff tree BruhatTits.tree Mumford.GraphAction Mumford.QuotEdge Mumford.QuotVert Mumford.ActsThrough Omega.IsThetaPair Omega.thetaMer Omega.IsDiscrete Omega.exists_holRing_div_eq_theta Omega.exists_monoidHom_fracAct_thetaMer_eq Omega.thetaMer_eq_mk_of_isThetaPair Omega.isDiscrete_of_finite_stabilizer_stdVertex BruhatTits.finite_setOf_dist_le BruhatTits.tree_connected_and_colorable_two BruhatTits.exists_pos_forall_isOfFinOrder_pow_eq_one Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter" namespace Omega p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane affinoid_mono mem_affinoid_iff' IsExhausted holRing coe_smul_upperHalfPlane HolRingOf HolRingOf.isDomain_iff merField pmoebius upperHalfPlane theta IsThetaPair thetaMer IsDiscrete exists_holRing_div_eq_theta exists_monoidHom_fracAct_thetaMer_eq thetaMer_eq_mk_of_isThetaPair isDiscrete_of_finite_stabilizer_stdVertex finite_setOf_pmoebius_mem_affinoid exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring" namespace SepGlue end CerednikDrinfeld.Omega.SepGlue
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.Omega" in
theorem CerednikDrinfeld.Omega.SepGlue.exists_basePoint
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : Omega.IsDiscrete K ρ)
    (z z' : ↥(Omega.upperHalfPlane K₀ K)) :
    ∃ z₀ : K, z₀ ∈ Omega.upperHalfPlane K₀ K ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) (z : K) ≠ z₀) ∧ (∀ γ : G, pmoebius K₀ (ρ γ) (z' : K) ≠ z₀) := by
  classical

  obtain ⟨n₁, hn₁⟩ := hex z z.2
  obtain ⟨n₂, hn₂⟩ := hex z' z'.2
  have hz : (z : K) ∈ affinoid ϖ (max n₁ n₂) := affinoid_mono ϖ (le_max_left _ _) hn₁
  have hz' : (z' : K) ∈ affinoid ϖ (max n₁ n₂) := affinoid_mono ϖ (le_max_right _ _) hn₂
  generalize max n₁ n₂ = N at hz hz'
  have hp0 : 0 < Valued.v (algebraMap K₀ K ϖ.ϖ) := ϖ.pos
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one

  let t : ℕ → K := fun k => algebraMap K₀ K (ϖ.ϖ ^ (N + 1 + k))
  have ht : ∀ k, Valued.v (t k) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (N + 1 + k) := fun k => by
    simp only [t, map_pow]
  have htlt : ∀ k, Valued.v (t k) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N := fun k => by
    rw [ht]; exact pow_lt_pow_right_of_lt_one₀ hp0 hp1 (by omega)
  let f : ℕ → K := fun k => (z : K) + t k
  have hf_inj : Function.Injective f := by
    intro a b hab
    have htab : t a = t b := add_left_cancel hab
    have hv : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (N + 1 + a) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (N + 1 + b) := by rw [← ht, ← ht, htab]
    have := (pow_right_strictAnti₀ hp0 hp1).injective hv
    omega

  have hfmem : ∀ k, f k ∈ affinoid ϖ N := by
    intro k
    have hzz := hz
    rw [mem_affinoid_iff'] at hzz ⊢
    obtain ⟨hz₁, hz₂⟩ := hzz
    refine ⟨?_, fun a => ?_⟩
    · refine (Valuation.map_add _ _ _).trans (max_le hz₁ ?_)
      rw [ht]
      exact (pow_le_one₀ zero_le' hp1.le).trans (one_le_pow₀ ((one_le_inv₀ hp0).2 hp1.le))
    · have hlt : Valued.v (t k) < Valued.v ((z : K) - algebraMap K₀ K a) := (htlt k).trans_le (hz₂ a)
      rw [show (z : K) + t k - algebraMap K₀ K a = ((z : K) - algebraMap K₀ K a) + t k by ring,
        Valuation.map_add_eq_of_lt_left _ hlt]
      exact hz₂ a

  have hA := finite_setOf_pmoebius_mem_affinoid ϖ ρ hρ N hz
  have hA' := finite_setOf_pmoebius_mem_affinoid ϖ ρ hρ N hz'
  have hB : (f ⁻¹' ((fun γ => pmoebius K₀ (ρ γ) (z : K)) '' {γ | pmoebius K₀ (ρ γ) (z : K) ∈ affinoid ϖ N} ∪
      (fun γ => pmoebius K₀ (ρ γ) (z' : K)) '' {γ | pmoebius K₀ (ρ γ) (z' : K) ∈ affinoid ϖ N})).Finite :=
    Set.Finite.preimage hf_inj.injOn ((hA.image _).union (hA'.image _))
  obtain ⟨k, -, hk⟩ := Set.infinite_univ.exists_notMem_finset hB.toFinset
  rw [Set.Finite.mem_toFinset] at hk
  refine ⟨f k, affinoid_subset_upperHalfPlane ϖ N (hfmem k), fun γ hγ => hk ?_, fun γ hγ => hk ?_⟩
  · exact Or.inl ⟨γ, by rw [Set.mem_setOf_eq, hγ]; exact hfmem k, hγ⟩
  · exact Or.inr ⟨γ, by rw [Set.mem_setOf_eq, hγ]; exact hfmem k, hγ⟩

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in
theorem sectionW_of_repr
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ) [IsDomain ↥(Omega.holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hdisc : Omega.IsDiscrete K ρ)
    (χ : G →* Kˣ) (S : Finset ↥(Omega.upperHalfPlane K₀ K))
    {n : ℕ} (a b : Fin n → K) (z₀ : K)
    (ha : ∀ i, a i ∈ Omega.upperHalfPlane K₀ K) (hb : ∀ i, b i ∈ Omega.upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ K)
    (hz₀a : ∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) (hz₀b : ∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀)
    (havoid : ∀ s ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s : K))
    (hχ : ∀ β : G, ((χ β : Kˣ) : K) = ∏ i, Omega.theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) :
    ∃ (F H : ↥(Omega.holRing ϖ)) (hH : H ∈ nonZeroDivisors ↥(Omega.holRing ϖ)),
      F ≠ 0 ∧
      (∀ w ∈ S, (F : ↥(Omega.upperHalfPlane K₀ K) → K) w ≠ 0 ∧ (H : ↥(Omega.upperHalfPlane K₀ K) → K) w ≠ 0) ∧
      ∀ γ : G,
        Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ γ) (Localization.mk F ⟨H, hH⟩) =
          algebraMap K (Omega.merField ϖ) (((χ γ)⁻¹ : Kˣ) : K) * Localization.mk F ⟨H, hH⟩ := by
  classical

  have hpair : ∀ i : Fin n, ∃ F H : ↥(Omega.holRing ϖ), Omega.IsThetaPair ϖ ρ (a i) (b i) z₀ F H := by
    intro i
    obtain ⟨F, H, h1, h2, h3, h4⟩ := CerednikDrinfeld.Omega.exists_holRing_div_eq_theta K₀ K ϖ hex ρ hdisc
      (ha i) (hb i) hz₀ (hz₀a i) (hz₀b i)
    exact ⟨F, H, h1, h2, h3, h4⟩
  choose Fi Hi hTP using hpair
  have hmult : ∀ i : Fin n, ∃ c : G →* Kˣ,
      (∀ β : G, ((c β : Kˣ) : K) = Omega.theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) ∧
      ∀ γ : G, Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ γ) (Omega.thetaMer ϖ ρ (a i) (b i) z₀) =
        algebraMap K (Omega.merField ϖ) (((c γ)⁻¹ : Kˣ) : K) * Omega.thetaMer ϖ ρ (a i) (b i) z₀ :=
    fun i => CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ K ϖ hex ρ hdisc (ha i) (hb i) hz₀ (hz₀a i) (hz₀b i)
  choose ci hci hcact using hmult
  have hΘi : ∀ i, Omega.thetaMer ϖ ρ (a i) (b i) z₀ = Localization.mk (Fi i) ⟨Hi i, (hTP i).1⟩ :=
    fun i => CerednikDrinfeld.Omega.thetaMer_eq_mk_of_isThetaPair ϖ ρ (a i) (b i) z₀ (Fi i) (Hi i) (hTP i)

  have hmv : ∀ (γ : G) (x : K) (hx : x ∈ Omega.upperHalfPlane K₀ K) (w : ↥(Omega.upperHalfPlane K₀ K)),
      pmoebius K₀ (ρ γ) x = (w : K) → x = pmoebius K₀ (ρ γ⁻¹) (w : K) := by
    intro γ x hx w h
    have h1 : (ρ γ) • (⟨x, hx⟩ : ↥(Omega.upperHalfPlane K₀ K)) = w := by
      apply Subtype.ext; rw [Omega.coe_smul_upperHalfPlane]; exact h
    rw [map_inv, ← Omega.coe_smul_upperHalfPlane, ← h1, inv_smul_smul]
  have hFne : ∀ i (w : ↥(Omega.upperHalfPlane K₀ K)), (∀ δ : G, a i ≠ pmoebius K₀ (ρ δ) (w : K)) →
      (Fi i : ↥(Omega.upperHalfPlane K₀ K) → K) w ≠ 0 := by
    intro i w hw h0
    obtain ⟨γ, hγ⟩ := ((hTP i).2.2.1 w).1 h0
    exact hw γ⁻¹ (hmv γ (a i) (ha i) w hγ)
  have hHne : ∀ i (w : ↥(Omega.upperHalfPlane K₀ K)), (∀ δ : G, b i ≠ pmoebius K₀ (ρ δ) (w : K)) →
      (Hi i : ↥(Omega.upperHalfPlane K₀ K) → K) w ≠ 0 := by
    intro i w hw h0
    obtain ⟨γ, hγ⟩ := ((hTP i).2.1 w).1 h0
    exact hw γ⁻¹ (hmv γ (b i) (hb i) w hγ)

  have hH₁ : (∏ i, Hi i : ↥(Omega.holRing ϖ)) ∈ nonZeroDivisors ↥(Omega.holRing ϖ) :=
    Submonoid.prod_mem _ fun i _ => (hTP i).1
  have hcoeF : ∀ w : ↥(Omega.upperHalfPlane K₀ K), ((∏ i, Fi i : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) w =
      ∏ i, (Fi i : ↥(Omega.upperHalfPlane K₀ K) → K) w := by
    intro w; rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
  have hcoeH : ∀ w : ↥(Omega.upperHalfPlane K₀ K), ((∏ i, Hi i : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) w =
      ∏ i, (Hi i : ↥(Omega.upperHalfPlane K₀ K) → K) w := by
    intro w; rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
  refine ⟨∏ i, Fi i, ∏ i, Hi i, hH₁, ?_, ?_, ?_⟩
  ·
    intro h0
    have h1 : ((∏ i, Fi i : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨z₀, hz₀⟩ = 0 := by rw [h0]; rfl
    rw [hcoeF, Finset.prod_eq_zero_iff] at h1
    obtain ⟨i, -, hi⟩ := h1
    obtain ⟨γ, hγ⟩ := ((hTP i).2.2.1 ⟨z₀, hz₀⟩).1 hi
    exact hz₀a i γ hγ
  · intro w hw
    refine ⟨?_, ?_⟩
    · rw [hcoeF, Finset.prod_ne_zero_iff]
      exact fun i _ => hFne i w fun δ => (havoid w hw i δ).1
    · rw [hcoeH, Finset.prod_ne_zero_iff]
      exact fun i _ => hHne i w fun δ => (havoid w hw i δ).2
  · intro γ
    have hinj : Function.Injective (algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ)) :=
      IsFractionRing.injective ↥(Omega.holRing ϖ) (Omega.merField ϖ)

    have hprod : (Localization.mk (∏ i, Fi i) ⟨∏ i, Hi i, hH₁⟩ : Omega.merField ϖ) =
        ∏ i, Omega.thetaMer ϖ ρ (a i) (b i) z₀ := by
      rw [Localization.mk_eq_mk'_apply, IsFractionRing.mk'_eq_div, map_prod, map_prod, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hΘi, Localization.mk_eq_mk'_apply, IsFractionRing.mk'_eq_div]

    have hcoeff : (((χ γ)⁻¹ : Kˣ) : K) = ∏ i, (((ci i γ)⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, hχ γ]
      rw [show (∏ i, Omega.theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ γ) z₀)) = ∏ i, ((ci i γ : Kˣ) : K) from
        Finset.prod_congr rfl fun i _ => (hci i γ).symm]
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => (Units.val_inv_eq_inv_val _).symm
    rw [hprod, map_prod, hcoeff, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hcact i γ

theorem sep_key {L : Type} [Field L] (φ : L ≃+* L) (aF aH aF₁ aH₁ u : L) (m : ℕ)
    (haH : aH ≠ 0) (haH₁ : aH₁ ≠ 0) (hu : u ≠ 0)
    (hΘ : φ (aF / aH) = u * (aF / aH)) (hs : φ (aF₁ / aH₁) = u ^ m * (aF₁ / aH₁)) :
    φ (aF ^ m * aH₁ / (aH ^ m * aF₁ + aF ^ m * aH₁)) = aF ^ m * aH₁ / (aH ^ m * aF₁ + aF ^ m * aH₁) := by
  have e1 : (aF / aH) ^ m / (aF₁ / aH₁ + (aF / aH) ^ m) = aF ^ m * aH₁ / (aH ^ m * aF₁ + aF ^ m * aH₁) := by
    rw [div_pow, div_add_div _ _ haH₁ (pow_ne_zero m haH), div_div_div_eq, ← mul_assoc,
      mul_comm (aH ^ m) (aF₁ * aH ^ m + aH₁ * aF ^ m), mul_div_mul_right _ _ (pow_ne_zero m haH)]
    congr 1
    ring
  rw [← e1, map_div₀, map_add, map_pow, hΘ, hs, mul_pow, ← mul_add, mul_div_mul_left _ _ (pow_ne_zero m hu)]

theorem fracAct_holRingOf_eq
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : Omega.PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)] [IsDomain ↥(Omega.holRing ϖ)] (γ : G) (x : FractionRing (Omega.HolRingOf ϖ ρ)) :
    Mumford.fracAct G (Omega.HolRingOf ϖ ρ) γ x = Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ γ) x := by
  have h : (Mumford.fracAct G (Omega.HolRingOf ϖ ρ) γ).toRingHom =
      (Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ γ)).toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Omega.HolRingOf ϖ ρ)) (RingHom.ext fun f => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [Mumford.fracAct_algebraMap]
    exact (Mumford.fracAct_algebraMap PGL(2, K₀) ↥(Omega.holRing ϖ) (ρ γ) f).symm
  exact congrArg (fun e : FractionRing (Omega.HolRingOf ϖ ρ) →+* FractionRing (Omega.HolRingOf ϖ ρ) => e x) h

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in
theorem sep_core
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    [Finite (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer (↥(Γ.map ρ)) w) : ℕ) : K) = 1) :
    ∀ z z' : ↥(Omega.upperHalfPlane K₀ K), (∀ γ : ↥(Γ.map ρ), z' ≠ (γ : PGL(2, K₀)) • z) →
      ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
        Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ ∧
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 ∧
        (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0 ∧ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 := by
  intro z z' hzz'
  classical
  haveI hdom : IsDomain ↥(Omega.holRing ϖ) := (Omega.HolRingOf.isDomain_iff ϖ ρ).1 inferInstance
  set Δ : Subgroup PGL(2, K₀) := Γ.map ρ with hΔ

  have hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N ≤ ε := by
    intro ε hε
    obtain ⟨y, hy0, hy⟩ := hval ε hε
    obtain ⟨N, hN⟩ := hrk (algebraMap K₀ K ϖ.ϖ) y ϖ.lt_one hy0
    exact ⟨N, hN.trans hy⟩

  haveI : Finite (R₀ ⧸ IsLocalRing.maximalIdeal R₀) := ‹Finite (IsLocalRing.ResidueField R₀)›
  haveI : Finite (R₀ ⧸ Ideal.span {ϖ₀}) :=
    Finite.of_equiv (R₀ ⧸ IsLocalRing.maximalIdeal R₀) (Ideal.quotEquivOfEq hϖ₀.maximalIdeal_eq).toEquiv
  have hint : ∀ a : R₀, Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ a)) ≤ 1 := fun a => (hR₀ _).1 ⟨a, rfl⟩
  have hv' : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R₀ a := by
    intro a ha
    obtain ⟨r, hr⟩ := (hR₀ a).2 ha
    exact ⟨r, hr⟩
  have hq' : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ ϖ₀)) ^ N ≤ ε := by
    rw [hϖ]; exact hq
  have hfinV : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Finite (MulAction.stabilizer ↥Δ w) :=
    CerednikDrinfeld.BruhatTits.StabExp.finite_stabilizer_vertex Δ hfin
  have hdisc : Omega.IsDiscrete K Δ.subtype := by
    haveI := hfinV (LT.LatticeTree.stdVertex R₀ K₀)
    have hst : {γ : ↥Δ | Δ.subtype γ • LT.LatticeTree.stdVertex R₀ K₀ = LT.LatticeTree.stdVertex R₀ K₀}.Finite :=
      (Set.toFinite (MulAction.stabilizer ↥Δ (LT.LatticeTree.stdVertex R₀ K₀) : Set ↥Δ)).subset fun γ hγ => hγ
    exact CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R₀ K₀ ϖ₀ hϖ₀ K hint hv' hq' Δ.subtype hst
  have hact : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) Δ.subtype := fun _ _ => rfl

  obtain ⟨z₀, hz₀, hz₀a, hz₀b⟩ := CerednikDrinfeld.Omega.SepGlue.exists_basePoint K₀ K ϖ hex Δ.subtype hdisc z z'

  obtain ⟨F, H, hH, hHz, hFz, hFH⟩ :=
    CerednikDrinfeld.Omega.exists_holRing_div_eq_theta K₀ K ϖ hex Δ.subtype hdisc z.2 z'.2 hz₀ hz₀a hz₀b
  have hTP : Omega.IsThetaPair ϖ Δ.subtype (z : K) (z' : K) z₀ F H := ⟨hH, hHz, hFz, hFH⟩
  have hΘ := CerednikDrinfeld.Omega.thetaMer_eq_mk_of_isThetaPair ϖ Δ.subtype (z : K) (z' : K) z₀ F H hTP

  obtain ⟨c, -, hcact⟩ :=
    CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ K ϖ hex Δ.subtype hdisc z.2 z'.2 hz₀ hz₀a hz₀b

  obtain ⟨m, hm, htors⟩ := CerednikDrinfeld.BruhatTits.exists_pos_forall_isOfFinOrder_pow_eq_one R₀ K₀ Δ hfin
  have hχ : ∀ γ : ↥Δ, IsOfFinOrder γ → ((powMonoidHom m).comp c) γ = 1 := by
    intro γ hγ
    show (c γ) ^ m = 1
    rw [← map_pow, htors γ hγ, map_one]

  have hcb2 := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  have hvt := CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    PGL(2, K₀) (BruhatTits.tree R₀ K₀) hcb2.1 hcb2.2 (LT.LatticeTree.stdVertex R₀ K₀)
  have hτ : ∀ (g : ↥Δ) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) =
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w :=
    fun g w => (Mumford.mem_typePreserving_iff _ _ _).1 (htp g.2) w
  have hadj : ∀ u w : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u w →
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := by
    intro u w huw h
    rw [hvt.1 u w huw] at h
    have h1 : (1 : ZMod 2) = 0 := by
      have := congrArg (fun t => t - Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u) h
      simpa using this.symm
    exact one_ne_zero h1

  obtain ⟨n, a, b, z₁, ha, hb, hz₁, hz₁a, hz₁b, havoid, hrepr⟩ :=
    CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring R₀ K₀ ϖ₀ hϖ₀ K hint hv' hq' hrk ϖ hex
      Δ.subtype hact hfinV (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτ hadj htame
      ((powMonoidHom m).comp c) hχ {z, z'}
  obtain ⟨F₁, H₁, hH₁, -, hS, hsect⟩ :=
    sectionW_of_repr K₀ K ϖ hex Δ.subtype hdisc ((powMonoidHom m).comp c) {z, z'} a b z₁ ha hb hz₁ hz₁a hz₁b havoid hrepr
  have hSz := hS z (Finset.mem_insert_self _ _)
  have hSz' := hS z' (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

  have hmv : ∀ (γ : ↥Δ) (w w' : ↥(Omega.upperHalfPlane K₀ K)),
      pmoebius K₀ (Δ.subtype γ) (w : K) = (w' : K) → (γ : PGL(2, K₀)) • w = w' := by
    intro γ w w' h
    apply Subtype.ext
    rw [Omega.coe_smul_upperHalfPlane]
    exact h
  have hp1 : ∀ w : ↥(Omega.upperHalfPlane K₀ K), pmoebius K₀ (Δ.subtype 1) (w : K) = (w : K) := by
    intro w
    rw [map_one, ← Omega.coe_smul_upperHalfPlane, one_smul]
  have hFz0 : (F : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0 := (hFz z).2 ⟨1, hp1 z⟩
  have hHz'0 : (H : ↥(Omega.upperHalfPlane K₀ K) → K) z' = 0 := (hHz z').2 ⟨1, hp1 z'⟩
  have hHz0 : (H : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 := by
    intro h0
    obtain ⟨γ, hγ⟩ := (hHz z).1 h0
    have h1 : (γ : PGL(2, K₀)) • z' = z := hmv γ z' z hγ
    apply hzz' γ⁻¹
    rw [Subgroup.coe_inv, eq_inv_smul_iff, h1]
  have hFz'0 : (F : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 := by
    intro h0
    obtain ⟨γ, hγ⟩ := (hFz z').1 h0
    exact hzz' γ (hmv γ z z' hγ).symm

  have hcoe : ∀ (A B : ↥(Omega.holRing ϖ)) (w : ↥(Omega.upperHalfPlane K₀ K)),
      ((A ^ m * B : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) w =
        (A : ↥(Omega.upperHalfPlane K₀ K) → K) w ^ m * (B : ↥(Omega.upperHalfPlane K₀ K) → K) w := by
    intro A B w
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, Pi.mul_apply, Pi.pow_apply]
  have hcoe2 : ∀ w : ↥(Omega.upperHalfPlane K₀ K),
      ((H ^ m * F₁ + F ^ m * H₁ : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) w =
        (H : ↥(Omega.upperHalfPlane K₀ K) → K) w ^ m * (F₁ : ↥(Omega.upperHalfPlane K₀ K) → K) w +
        (F : ↥(Omega.upperHalfPlane K₀ K) → K) w ^ m * (H₁ : ↥(Omega.upperHalfPlane K₀ K) → K) w := by
    intro w
    rw [Subring.coe_add, Pi.add_apply, hcoe, hcoe]
  have hhz : ((H ^ m * F₁ + F ^ m * H₁ : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 := by
    rw [hcoe2, hFz0, zero_pow hm.ne', zero_mul, add_zero]
    exact mul_ne_zero (pow_ne_zero _ hHz0) hSz.1
  have hhz' : ((H ^ m * F₁ + F ^ m * H₁ : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 := by
    rw [hcoe2, hHz'0, zero_pow hm.ne', zero_mul, zero_add]
    exact mul_ne_zero (pow_ne_zero _ hFz'0) hSz'.2
  have hgz : ((F ^ m * H₁ : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0 := by
    rw [hcoe, hFz0, zero_pow hm.ne', zero_mul]
  have hgz' : ((F ^ m * H₁ : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 := by
    rw [hcoe]; exact mul_ne_zero (pow_ne_zero _ hFz'0) hSz'.2
  have hh0 : (H ^ m * F₁ + F ^ m * H₁ : ↥(Omega.holRing ϖ)) ≠ 0 := by
    intro h0; apply hhz; rw [h0]; rfl
  have hh : (H ^ m * F₁ + F ^ m * H₁ : ↥(Omega.holRing ϖ)) ∈ nonZeroDivisors ↥(Omega.holRing ϖ) :=
    mem_nonZeroDivisors_of_ne_zero hh0

  have hH0 : H ≠ 0 := nonZeroDivisors.ne_zero hH
  have hH₁0 : H₁ ≠ 0 := nonZeroDivisors.ne_zero hH₁
  have hinj : Function.Injective (algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ)) :=
    IsFractionRing.injective ↥(Omega.holRing ϖ) (Omega.merField ϖ)
  have haH : algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H ≠ 0 := (map_ne_zero_iff _ hinj).2 hH0
  have haH₁ : algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H₁ ≠ 0 := (map_ne_zero_iff _ hinj).2 hH₁0
  have hmkΘ : Omega.thetaMer ϖ Δ.subtype (z : K) (z' : K) z₀ =
      algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) F / algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H := by
    rw [hΘ, Localization.mk_eq_mk'_apply, IsFractionRing.mk'_eq_div]
  have hmks : (Localization.mk F₁ ⟨H₁, hH₁⟩ : Omega.merField ϖ) =
      algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) F₁ / algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H₁ := by
    rw [Localization.mk_eq_mk'_apply, IsFractionRing.mk'_eq_div]
  have hmkx : (Localization.mk (F ^ m * H₁) ⟨H ^ m * F₁ + F ^ m * H₁, hh⟩ : Omega.merField ϖ) =
      algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) F ^ m * algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H₁ /
        (algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H ^ m * algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) F₁ +
          algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) F ^ m * algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H₁) := by
    rw [Localization.mk_eq_mk'_apply, IsFractionRing.mk'_eq_div]
    simp only [map_mul, map_add, map_pow]
  have hinv : ∀ δ : ↥Δ, Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (δ : PGL(2, K₀))
      (Localization.mk (F ^ m * H₁) ⟨H ^ m * F₁ + F ^ m * H₁, hh⟩) =
      Localization.mk (F ^ m * H₁) ⟨H ^ m * F₁ + F ^ m * H₁, hh⟩ := by
    intro δ
    have hu : (algebraMap K (Omega.merField ϖ)) (((c δ)⁻¹ : Kˣ) : K) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K (Omega.merField ϖ)).injective).2 (Units.ne_zero _)
    have h1 := hcact δ
    rw [hmkΘ] at h1
    have h2 : Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (δ : PGL(2, K₀))
        (algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) F₁ / algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H₁) =
        algebraMap K (Omega.merField ϖ) (((c δ)⁻¹ : Kˣ) : K) ^ m *
          (algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) F₁ / algebraMap ↥(Omega.holRing ϖ) (Omega.merField ϖ) H₁) := by
      have hcoeff : ((((powMonoidHom m).comp c δ)⁻¹ : Kˣ) : K) = (((c δ)⁻¹ : Kˣ) : K) ^ m := by
        rw [MonoidHom.comp_apply, powMonoidHom_apply, ← inv_pow, Units.val_pow_eq_pow_val]
      rw [← hmks]
      have h3 := hsect δ
      rw [hcoeff, map_pow] at h3
      exact h3
    rw [hmkx]
    exact sep_key (Mumford.fracAct PGL(2, K₀) ↥(Omega.holRing ϖ) (δ : PGL(2, K₀))) _ _ _ _ _ m haH haH₁ hu h1 h2

  refine ⟨F ^ m * H₁, H ^ m * F₁ + F ^ m * H₁, hh, ?_, hhz, hhz', hgz, hgz'⟩
  rw [Mumford.mem_invariantFieldOf_iff]
  intro γ hγ
  rw [Mumford.frac_smul_def, fracAct_holRingOf_eq]
  exact hinv ⟨ρ γ, Subgroup.mem_map_of_mem ρ hγ⟩

theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))

    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer (↥(Γ.map ρ)) w) : ℕ) : K) = 1)
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))] :
    ∀ z z' : ↥(Omega.upperHalfPlane K₀ K), (∀ γ : ↥(Γ.map ρ), z' ≠ (γ : PGL(2, K₀)) • z) →
      ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
        Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ ∧
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 ∧
        (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z = 0 ∧ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ K) → K) z' ≠ 0 := by
  intro z z' hzz'
  haveI : Finite (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) := inferInstance
  exact sep_core K₀ K hrk hval R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex G ρ Γ htp hfin htame z z' hzz'

end S_CerednikDrinfeld_Omega_exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_mem_invariantFieldOf_apply_eq_zero_and_apply_ne_zero_of_forall_ne_smul_of_map_le_typePreserving_of_exists_v_le_of_v_card_stabilizer_eq_one (solution)
