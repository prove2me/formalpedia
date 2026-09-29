-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_finiteHom_quotientDegeneracyData_of_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/62b4fe9b-c2e4-520c-a42d-34999abd6e96

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup

set_option autoImplicit false

noncomputable section

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford ModularCurve MulAction"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "DegeneracyData degeneracyMatrix pushforward jointDelta ribbonKernel mem_ribbonKernel"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "GraphAction QuotEdge QuotVert card_stabilizer_smul stabWidth stabWidth_mk quotientDegeneracyData"
namespace I4a
namespace OrbitCount
p2m_open "CerednikDrinfeld.Mumford CerednikDrinfeld"

variable {H : Type} [Group H] (K : Subgroup H) {Y : Type} [MulAction H Y]

theorem subgroup_smul (k : ↥K) (y : Y) : k • y = (k : H) • y := rfl

def psi (y₀ : Y) : H ⧸ K → orbitRel.Quotient K Y :=
  Quotient.lift (s := QuotientGroup.leftRel K)
    (fun h : H => (Quotient.mk (orbitRel K Y) (h⁻¹ • y₀) : orbitRel.Quotient K Y))
    (fun a b hab => by
      have hab' : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
      apply Quotient.sound
      refine ⟨⟨a⁻¹ * b, hab'⟩, ?_⟩
      show (a⁻¹ * b) • (b⁻¹ • y₀) = a⁻¹ • y₀
      rw [smul_smul, mul_assoc, mul_inv_cancel, mul_one])

theorem psi_mk (y₀ : Y) (h : H) : psi K y₀ (QuotientGroup.mk h) = Quotient.mk (orbitRel K Y) (h⁻¹ • y₀) := rfl

def fibreMap (y₀ y : Y) (g : H) (hg : g • y₀ = y) :
    ↥(stabilizer H y) ⧸ (K.subgroupOf (stabilizer H y)) → {c : H ⧸ K // psi K y₀ c = Quotient.mk (orbitRel K Y) y} :=
  Quotient.lift (s := QuotientGroup.leftRel (K.subgroupOf (stabilizer H y)))
    (fun s : ↥(stabilizer H y) => ⟨QuotientGroup.mk (g⁻¹ * (s : H)), by
      rw [psi_mk, mul_inv_rev, inv_inv, ← smul_smul, hg]
      congr 1
      exact (mem_stabilizer_iff.mp (inv_mem s.2))⟩)
    (fun a b hab => by
      have hab₀ : a⁻¹ * b ∈ K.subgroupOf (stabilizer H y) := QuotientGroup.leftRel_apply.mp hab
      have hab' : ((a⁻¹ * b : ↥(stabilizer H y)) : H) ∈ K := Subgroup.mem_subgroupOf.mp hab₀
      apply Subtype.ext
      apply QuotientGroup.eq.mpr
      have : (g⁻¹ * (a : H))⁻¹ * (g⁻¹ * (b : H)) = (a : H)⁻¹ * (b : H) := by group
      rw [this]
      exact hab')

theorem fibreMap_mk (y₀ y : Y) (g : H) (hg : g • y₀ = y) (s : ↥(stabilizer H y)) :
    ((fibreMap K y₀ y g hg (QuotientGroup.mk s)) : H ⧸ K) = QuotientGroup.mk (g⁻¹ * (s : H)) := rfl

theorem fibreMap_bijective (y₀ y : Y) (g : H) (hg : g • y₀ = y) : Function.Bijective (fibreMap K y₀ y g hg) := by
  constructor
  · intro p q hpq
    induction p using QuotientGroup.induction_on with
    | H a =>
    induction q using QuotientGroup.induction_on with
    | H b =>
    have h1 := congrArg (fun c : {c : H ⧸ K // psi K y₀ c = Quotient.mk (orbitRel K Y) y} => (c : H ⧸ K)) hpq
    simp only [fibreMap_mk] at h1
    have h2 : (g⁻¹ * (a : H))⁻¹ * (g⁻¹ * (b : H)) ∈ K := QuotientGroup.eq.mp h1
    have h3 : (g⁻¹ * (a : H))⁻¹ * (g⁻¹ * (b : H)) = (a : H)⁻¹ * (b : H) := by group
    rw [h3] at h2
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr (Subgroup.mem_subgroupOf.mpr h2)
  · rintro ⟨c, hc⟩
    induction c using QuotientGroup.induction_on with
    | H h =>
    rw [psi_mk] at hc
    have hk := Quotient.exact hc

    obtain ⟨k, hk⟩ := hk
    have hk' : (k : H) • y = h⁻¹ • y₀ := hk
    have hs : g * h * (k : H) ∈ stabilizer H y := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hk', smul_smul h, mul_inv_cancel, one_smul, hg]
    refine ⟨QuotientGroup.mk ⟨g * h * (k : H), hs⟩, ?_⟩
    apply Subtype.ext
    rw [fibreMap_mk]
    apply QuotientGroup.eq.mpr
    show (g⁻¹ * (g * h * (k : H)))⁻¹ * h ∈ K
    have : (g⁻¹ * (g * h * (k : H)))⁻¹ * h = (k : H)⁻¹ := by group
    rw [this]
    exact inv_mem k.2

theorem sum_relIndex_stabilizer_eq_index [K.FiniteIndex] [Fintype (orbitRel.Quotient K Y)] (y₀ : Y)
    (htrans : ∀ y : Y, ∃ h : H, h • y₀ = y) :
    (∑ O : orbitRel.Quotient K Y, K.relIndex (stabilizer H O.out)) = K.index := by
  classical
  haveI : Fintype (H ⧸ K) := Fintype.ofFinite (H ⧸ K)
  rw [Subgroup.index, Nat.card_eq_fintype_card, Fintype.card_congr (Equiv.sigmaFiberEquiv (psi K y₀)).symm,
    Fintype.card_sigma]
  refine Finset.sum_congr rfl fun O _ => ?_
  have hO : Quotient.mk (orbitRel K Y) O.out = O := Quotient.out_eq O
  have hg := htrans O.out
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (Equiv.ofBijective _ (fibreMap_bijective K y₀ O.out hg.choose hg.choose_spec)),
    Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun c => by rw [hO]))

end CerednikDrinfeld.Mumford.I4a.OrbitCount

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "DegeneracyData degeneracyMatrix pushforward jointDelta ribbonKernel mem_ribbonKernel"
p2m_open "CerednikDrinfeld"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "GraphAction QuotEdge QuotVert card_stabilizer_smul stabWidth stabWidth_mk quotientDegeneracyData"
p2m_open "CerednikDrinfeld.Mumford"
namespace I4a

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W} [GraphAction G 𝒯]
  {Γ' : Subgroup G} [GraphAction (↥Γ') 𝒯]

section Generic
variable {E V : Type} [Fintype E] [DecidableEq V]

theorem pushforward_apply (f : E → V) (x : E → ℤ) (v : V) :
    pushforward f x v = ∑ e : E, if f e = v then x e else 0 := by
  simp only [pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply,
    ite_mul, one_mul, zero_mul]

theorem mem_ribbonKernel_iff' (D : DegeneracyData E V) (x : E → ℤ) :
    x ∈ ribbonKernel D ↔ pushforward D.a x = 0 ∧ pushforward D.b x = 0 := by
  rw [mem_ribbonKernel]
  constructor
  · intro h
    exact ⟨by simpa [jointDelta] using h 0, by simpa [jointDelta] using h 1⟩
  · rintro ⟨ha, hb⟩ i
    fin_cases i
    · simpa [jointDelta] using ha
    · simpa [jointDelta] using hb

end Generic

theorem subgroup_smul_dart (γ : ↥Γ') (d : 𝒯.Dart) : γ • d = (γ : G) • d := rfl

theorem mem_stabilizer_subgroup_iff (γ : ↥Γ') (d : 𝒯.Dart) :
    γ ∈ stabilizer (↥Γ') d ↔ (γ : G) ∈ stabilizer G d := Iff.rfl

theorem card_stabilizer_subgroup (d : 𝒯.Dart) :
    Nat.card (stabilizer (↥Γ') d) = Nat.card ↥(Γ'.subgroupOf (stabilizer G d)) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨⟨(γ : ↥Γ'), (mem_stabilizer_subgroup_iff _ d).mp γ.2⟩, by
        show ((γ : ↥Γ') : G) ∈ Γ'; exact (γ : ↥Γ').2⟩
      invFun := fun s => ⟨⟨((s : ↥(stabilizer G d)) : G), s.2⟩, by
        show (((s : ↥(stabilizer G d)) : G)) ∈ stabilizer G d; exact (s : ↥(stabilizer G d)).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_stabilizer_eq_mul (d : 𝒯.Dart) :
    Nat.card (stabilizer G d) = Nat.card (stabilizer (↥Γ') d) * Γ'.relIndex (stabilizer G d) := by
  rw [card_stabilizer_subgroup, Subgroup.relIndex]
  exact (Subgroup.card_mul_index (Γ'.subgroupOf (stabilizer G d))).symm

theorem relIndex_stabilizer_smul (γ : ↥Γ') (d : 𝒯.Dart) (hfin : Finite (stabilizer G d)) :
    Γ'.relIndex (stabilizer G ((γ : G) • d)) = Γ'.relIndex (stabilizer G d) := by
  have h1 := card_stabilizer_eq_mul (Γ' := Γ') ((γ : G) • d)
  have h2 := card_stabilizer_eq_mul (Γ' := Γ') d
  rw [card_stabilizer_smul] at h1
  have h3 : Nat.card (stabilizer (↥Γ') ((γ : G) • d)) = Nat.card (stabilizer (↥Γ') d) := by
    rw [← subgroup_smul_dart]; exact card_stabilizer_smul 𝒯 γ d
  rw [h3] at h1
  haveI : Finite (stabilizer (↥Γ') d) := Finite.of_injective (fun γ : stabilizer (↥Γ') d =>
    (⟨((γ : ↥Γ') : G), (mem_stabilizer_subgroup_iff _ d).mp γ.2⟩ : stabilizer G d))
    (fun a b h => by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun s : stabilizer G d => (s : G)) h)
  have hpos : 0 < Nat.card (stabilizer (↥Γ') d) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)

variable (G Γ') in

def piq : QuotEdge (↥Γ') 𝒯 → QuotEdge G 𝒯 :=
  Quotient.map' id (fun _ _ h => by obtain ⟨γ, h⟩ := h; exact ⟨(γ : G), h⟩)

theorem piq_mk (d : 𝒯.Dart) : piq G Γ' (Quotient.mk (orbitRel (↥Γ') 𝒯.Dart) d) = Quotient.mk (orbitRel G 𝒯.Dart) d := rfl

theorem piq_eq_mk_out (e' : QuotEdge (↥Γ') 𝒯) :
    piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) e'.out := by
  conv_lhs => rw [← Quotient.out_eq e']
  rfl

variable (G Γ') in

def nq (e' : QuotEdge (↥Γ') 𝒯) : ℕ := Γ'.relIndex (stabilizer G e'.out)

theorem nq_mk (d : 𝒯.Dart) (hfin : Finite (stabilizer G d)) :
    nq G Γ' (Quotient.mk (orbitRel (↥Γ') 𝒯.Dart) d) = Γ'.relIndex (stabilizer G d) := by
  unfold nq
  have h : (orbitRel (↥Γ') 𝒯.Dart) (Quotient.mk (orbitRel (↥Γ') 𝒯.Dart) d).out d := Quotient.mk_out d
  obtain ⟨γ, hγ⟩ := h
  change γ • d = _ at hγ
  rw [← hγ, subgroup_smul_dart]
  exact relIndex_stabilizer_smul γ d hfin

theorem width_eq_mul (e' : QuotEdge (↥Γ') 𝒯) (hfin : Finite (stabilizer G e'.out)) :
    ((quotientDegeneracyData G 𝒯).w (Quotient.mk (orbitRel G 𝒯.Dart) e'.out) : ℕ) =
      ((quotientDegeneracyData (↥Γ') 𝒯).w e' : ℕ) * nq G Γ' e' := by
  haveI := hfin
  haveI : Finite (stabilizer (↥Γ') e'.out) := Finite.of_injective (fun γ : stabilizer (↥Γ') e'.out =>
    (⟨((γ : ↥Γ') : G), (mem_stabilizer_subgroup_iff _ _).mp γ.2⟩ : stabilizer G e'.out))
    (fun a b h => by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun s : stabilizer G e'.out => (s : G)) h)
  show (stabWidth G 𝒯 (Quotient.mk'' e'.out) : ℕ) = (stabWidth (↥Γ') 𝒯 e' : ℕ) * nq G Γ' e'
  rw [stabWidth_mk, stabWidth, nq, Nat.toPNat'_coe, Nat.toPNat'_coe, if_pos Nat.card_pos, if_pos Nat.card_pos]
  exact card_stabilizer_eq_mul e'.out

section InstA
variable (d₀ : 𝒯.Dart)

theorem stabilizer_orbitElem (y : ↥(orbit G d₀)) : stabilizer G y = stabilizer G (y : 𝒯.Dart) := by
  ext g
  simp only [mem_stabilizer_iff, Subtype.ext_iff, orbit.coe_smul]

variable (Γ') in

def phiA : orbitRel.Quotient (↥Γ') ↥(orbit G d₀) → QuotEdge (↥Γ') 𝒯 :=
  Quotient.map' (fun y => (y : 𝒯.Dart)) (fun a b h => by
    obtain ⟨γ, h⟩ := h
    exact ⟨γ, by rw [← h]; rfl⟩)

theorem phiA_mk (y : ↥(orbit G d₀)) :
    phiA Γ' d₀ (Quotient.mk (orbitRel (↥Γ') ↥(orbit G d₀)) y) = Quotient.mk (orbitRel (↥Γ') 𝒯.Dart) (y : 𝒯.Dart) := rfl

theorem piq_phiA (O : orbitRel.Quotient (↥Γ') ↥(orbit G d₀)) :
    piq G Γ' (phiA Γ' d₀ O) = Quotient.mk (orbitRel G 𝒯.Dart) d₀ := by
  induction O using Quotient.inductionOn with
  | h y =>
  rw [phiA_mk, piq_mk]
  exact Quotient.sound (orbitRel_apply.mpr y.2)

theorem phiA_injective : Function.Injective (phiA Γ' d₀) := by
  intro O O' h
  induction O using Quotient.inductionOn with
  | h y =>
  induction O' using Quotient.inductionOn with
  | h y' =>
  rw [phiA_mk, phiA_mk] at h
  obtain ⟨γ, hγ⟩ := Quotient.exact h
  apply Quotient.sound
  refine ⟨γ, ?_⟩
  apply Subtype.ext
  exact hγ

theorem phiA_surjOn [DecidableEq (QuotEdge G 𝒯)] (e' : QuotEdge (↥Γ') 𝒯)
    (he' : piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) d₀) :
    ∃ O, phiA Γ' d₀ O = e' := by
  have hmem : e'.out ∈ orbit G d₀ := by
    rw [piq_eq_mk_out] at he'
    exact orbitRel_apply.mp (Quotient.exact he')
  refine ⟨Quotient.mk _ ⟨e'.out, hmem⟩, ?_⟩
  rw [phiA_mk]
  exact Quotient.out_eq e'

end InstA

theorem sum_nq_fibre_eq_index [Γ'.FiniteIndex] [Fintype (QuotEdge (↥Γ') 𝒯)] [DecidableEq (QuotEdge G 𝒯)]
    (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) (e : QuotEdge G 𝒯) :
    (∑ e' ∈ Finset.univ.filter (fun e' : QuotEdge (↥Γ') 𝒯 => piq G Γ' e' = e), nq G Γ' e') = Γ'.index := by
  classical

  have he : e = Quotient.mk (orbitRel G 𝒯.Dart) e.out := (Quotient.out_eq e).symm
  rw [he]
  haveI : Fintype (orbitRel.Quotient (↥Γ') ↥(orbit G e.out)) := Fintype.ofInjective _ (phiA_injective e.out)
  rw [Finset.sum_subtype (Finset.univ.filter (fun e' : QuotEdge (↥Γ') 𝒯 => piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) e.out))
      (p := fun e' => piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) e.out) (fun e' => by simp)]
  rw [← Fintype.sum_bijective (fun O => (⟨phiA Γ' e.out O, piq_phiA e.out O⟩ :
        {e' : QuotEdge (↥Γ') 𝒯 // piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) e.out}))
      ⟨fun O O' h => phiA_injective e.out (congrArg Subtype.val h),
       fun t => by
        obtain ⟨O, hO⟩ := phiA_surjOn e.out t.1 t.2
        exact ⟨O, Subtype.ext hO⟩⟩
      (fun O => Γ'.relIndex (stabilizer G O.out)) (fun t => nq G Γ' t.1) ?_]
  · exact OrbitCount.sum_relIndex_stabilizer_eq_index Γ' ⟨e.out, mem_orbit_self e.out⟩
      (fun y => by
        obtain ⟨g, hg⟩ := mem_orbit_iff.mp y.2
        exact ⟨g, Subtype.ext hg⟩)
  · intro O
    show Γ'.relIndex (stabilizer G O.out) = nq G Γ' (phiA Γ' e.out O)
    conv_rhs => rw [← Quotient.out_eq O, phiA_mk]
    rw [nq_mk _ (hfinD _), stabilizer_orbitElem]

section InstB
variable (p : 𝒯.Dart →[G] W) (vt : W) (d₀ : 𝒯.Dart)

def YB : Type := {d : 𝒯.Dart // p d = vt ∧ d ∈ orbit G d₀}

scoped instance mulActionYB : MulAction ↥(stabilizer G vt) (YB p vt d₀) where
  smul s y := ⟨(s : G) • y.1, by
    refine ⟨by rw [map_smul, y.2.1]; exact mem_stabilizer_iff.mp s.2, ?_⟩
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp y.2.2
    exact mem_orbit_iff.mpr ⟨(s : G) * g, by rw [mul_smul, hg]⟩⟩
  one_smul y := Subtype.ext (one_smul G y.1)
  mul_smul s t y := Subtype.ext (mul_smul (s : G) (t : G) y.1)

theorem coe_smul_YB (s : ↥(stabilizer G vt)) (y : YB p vt d₀) : ((s • y : YB p vt d₀).1 : 𝒯.Dart) = (s : G) • y.1 := rfl

theorem stabilizer_le_of_YB (y : YB p vt d₀) : stabilizer G y.1 ≤ stabilizer G vt := by
  intro g hg
  rw [mem_stabilizer_iff] at hg ⊢
  rw [← y.2.1, ← map_smul, hg]

theorem card_stabilizer_YB (y : YB p vt d₀) :
    Nat.card (stabilizer (↥(stabilizer G vt)) y) = Nat.card (stabilizer G y.1) := by
  refine Nat.card_congr
    { toFun := fun s => ⟨((s : ↥(stabilizer G vt)) : G), by
        have := s.2; rw [mem_stabilizer_iff] at this ⊢; exact congrArg Subtype.val this⟩
      invFun := fun g => ⟨⟨(g : G), stabilizer_le_of_YB p vt d₀ y g.2⟩, by
        rw [mem_stabilizer_iff]; apply Subtype.ext; exact mem_stabilizer_iff.mp g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_subgroupOf_stabilizer_YB (y : YB p vt d₀) :
    Nat.card ↥((Γ'.subgroupOf (stabilizer G vt)).subgroupOf (stabilizer (↥(stabilizer G vt)) y)) =
      Nat.card ↥(Γ'.subgroupOf (stabilizer G y.1)) := by
  refine Nat.card_congr
    { toFun := fun s => ⟨⟨(((s : ↥(stabilizer (↥(stabilizer G vt)) y)) : ↥(stabilizer G vt)) : G), by
          have := (s : ↥(stabilizer (↥(stabilizer G vt)) y)).2
          rw [mem_stabilizer_iff] at this ⊢; exact congrArg Subtype.val this⟩,
        by exact Subgroup.mem_subgroupOf.mp s.2⟩
      invFun := fun g => ⟨⟨⟨((g : ↥(stabilizer G y.1)) : G), stabilizer_le_of_YB p vt d₀ y (g : ↥(stabilizer G y.1)).2⟩, by
          rw [mem_stabilizer_iff]; apply Subtype.ext; exact mem_stabilizer_iff.mp (g : ↥(stabilizer G y.1)).2⟩,
        by exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp g.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem relIndex_YB (y : YB p vt d₀) (hfin : Finite (stabilizer G y.1)) :
    (Γ'.subgroupOf (stabilizer G vt)).relIndex (stabilizer (↥(stabilizer G vt)) y) = Γ'.relIndex (stabilizer G y.1) := by
  have h1 := Subgroup.card_mul_index ((Γ'.subgroupOf (stabilizer G vt)).subgroupOf (stabilizer (↥(stabilizer G vt)) y))
  have h2 := Subgroup.card_mul_index (Γ'.subgroupOf (stabilizer G y.1))
  rw [card_subgroupOf_stabilizer_YB, card_stabilizer_YB] at h1
  rw [Subgroup.relIndex, Subgroup.relIndex]
  haveI := hfin
  haveI : Finite ↥(Γ'.subgroupOf (stabilizer G y.1)) := inferInstance
  have hpos : 0 < Nat.card ↥(Γ'.subgroupOf (stabilizer G y.1)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

variable (Γ') in

def phiB : orbitRel.Quotient ↥(Γ'.subgroupOf (stabilizer G vt)) (YB p vt d₀) → QuotEdge (↥Γ') 𝒯 :=
  Quotient.map' (fun y : YB p vt d₀ => y.1) (fun a b h => by
    obtain ⟨k, hk⟩ := h
    refine ⟨⟨(((k : ↥(Γ'.subgroupOf (stabilizer G vt))) : ↥(stabilizer G vt)) : G), Subgroup.mem_subgroupOf.mp k.2⟩, ?_⟩
    show ((((k : ↥(Γ'.subgroupOf (stabilizer G vt))) : ↥(stabilizer G vt)) : G)) • b.1 = a.1
    rw [← hk]; rfl)

theorem phiB_mk (y : YB p vt d₀) :
    phiB Γ' p vt d₀ (Quotient.mk _ y) = Quotient.mk (orbitRel (↥Γ') 𝒯.Dart) y.1 := rfl

variable (Γ') in

def qmapΓ : QuotEdge (↥Γ') 𝒯 → QuotVert (↥Γ') W :=
  Quotient.map' p (fun a b h => by obtain ⟨γ, h⟩ := h; exact ⟨γ, by rw [← h]; exact (map_smul p (γ : G) b).symm⟩)

variable (G) in

def qmapG : QuotEdge G 𝒯 → QuotVert G W :=
  Quotient.map' p (fun a b h => by obtain ⟨g, h⟩ := h; exact ⟨g, by rw [← h]; exact (map_smul p g b).symm⟩)

theorem qmapΓ_mk (d : 𝒯.Dart) : qmapΓ Γ' p (Quotient.mk _ d) = Quotient.mk (orbitRel (↥Γ') W) (p d) := rfl
theorem qmapG_mk (d : 𝒯.Dart) : qmapG G p (Quotient.mk _ d) = Quotient.mk (orbitRel G W) (p d) := rfl

theorem phiB_mem (O : orbitRel.Quotient ↥(Γ'.subgroupOf (stabilizer G vt)) (YB p vt d₀)) :
    piq G Γ' (phiB Γ' p vt d₀ O) = Quotient.mk (orbitRel G 𝒯.Dart) d₀ ∧
      qmapΓ Γ' p (phiB Γ' p vt d₀ O) = Quotient.mk (orbitRel (↥Γ') W) vt := by
  induction O using Quotient.inductionOn with
  | h y =>
  rw [phiB_mk, piq_mk, qmapΓ_mk, y.2.1]
  exact ⟨Quotient.sound (orbitRel_apply.mpr y.2.2), rfl⟩

theorem phiB_injective : Function.Injective (phiB Γ' p vt d₀) := by
  intro O O' h
  induction O using Quotient.inductionOn with
  | h y =>
  induction O' using Quotient.inductionOn with
  | h y' =>
  rw [phiB_mk, phiB_mk] at h
  obtain ⟨γ, hγ⟩ := Quotient.exact h
  have hγ' : (γ : G) • y'.1 = y.1 := hγ
  have hS : (γ : G) ∈ stabilizer G vt := by
    rw [mem_stabilizer_iff, ← y'.2.1, ← map_smul, hγ', y.2.1, y'.2.1]
  apply Quotient.sound
  refine ⟨⟨⟨(γ : G), hS⟩, Subgroup.mem_subgroupOf.mpr γ.2⟩, ?_⟩
  apply Subtype.ext
  exact hγ'

theorem phiB_surjOn [DecidableEq (QuotEdge G 𝒯)] (e' : QuotEdge (↥Γ') 𝒯)
    (h1 : piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) d₀) (h2 : qmapΓ Γ' p e' = Quotient.mk (orbitRel (↥Γ') W) vt) :
    ∃ O, phiB Γ' p vt d₀ O = e' := by
  have hd : e'.out ∈ orbit G d₀ := by
    rw [piq_eq_mk_out] at h1
    exact orbitRel_apply.mp (Quotient.exact h1)
  have h2' : Quotient.mk (orbitRel (↥Γ') W) (p e'.out) = Quotient.mk (orbitRel (↥Γ') W) vt := by
    rw [← qmapΓ_mk, Quotient.out_eq]; exact h2
  obtain ⟨γ, hγ⟩ := Quotient.exact h2'.symm

  have hγ' : (γ : G) • p e'.out = vt := hγ
  have hy : p ((γ : G) • e'.out) = vt ∧ (γ : G) • e'.out ∈ orbit G d₀ := by
    refine ⟨by rw [map_smul, hγ'], ?_⟩
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp hd
    exact mem_orbit_iff.mpr ⟨(γ : G) * g, by rw [mul_smul, hg]⟩
  refine ⟨Quotient.mk _ ⟨(γ : G) • e'.out, hy⟩, ?_⟩
  rw [phiB_mk]
  conv_rhs => rw [← Quotient.out_eq e']
  apply Quotient.sound
  exact ⟨γ, rfl⟩

theorem sum_nq_fibre_p [Fintype (QuotEdge (↥Γ') 𝒯)] [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert (↥Γ') W)]
    [DecidableEq (QuotVert G W)]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    (e : QuotEdge G 𝒯) :
    (∑ e' ∈ (Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 => qmapΓ Γ' p e' = Quotient.mk (orbitRel (↥Γ') W) vt).filter
        (fun e' => piq G Γ' e' = e), nq G Γ' e') =
      if qmapG G p e = Quotient.mk (orbitRel G W) vt then Γ'.relIndex (stabilizer G vt) else 0 := by
  classical
  by_cases hcase : qmapG G p e = Quotient.mk (orbitRel G W) vt
  · rw [if_pos hcase]

    have hex : ∃ d₀ : 𝒯.Dart, Quotient.mk (orbitRel G 𝒯.Dart) d₀ = e ∧ p d₀ = vt := by
      have h := hcase
      rw [← Quotient.out_eq e, qmapG_mk] at h
      obtain ⟨g, hg⟩ := Quotient.exact h.symm
      have hg' : g • p e.out = vt := hg
      refine ⟨g • e.out, ?_, by rw [map_smul, hg']⟩
      conv_rhs => rw [← Quotient.out_eq e]
      exact Quotient.sound ⟨g, rfl⟩
    obtain ⟨d₀, hd₀e, hd₀⟩ := hex
    rw [← hd₀e]
    haveI : Finite ↥(stabilizer G vt) := hfinV vt
    haveI : Fintype (orbitRel.Quotient ↥(Γ'.subgroupOf (stabilizer G vt)) (YB p vt d₀)) :=
      Fintype.ofInjective _ (phiB_injective p vt d₀)
    let T : Finset (QuotEdge (↥Γ') 𝒯) := (Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 =>
      qmapΓ Γ' p e' = Quotient.mk (orbitRel (↥Γ') W) vt).filter (fun e' => piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) d₀)
    have hT : ∀ e', e' ∈ T ↔ (piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) d₀ ∧ qmapΓ Γ' p e' = Quotient.mk (orbitRel (↥Γ') W) vt) := by
      intro e'; simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact And.comm
    show (∑ e' ∈ T, nq G Γ' e') = _
    rw [Finset.sum_subtype T hT]
    rw [← Fintype.sum_bijective (fun O => (⟨phiB Γ' p vt d₀ O, phiB_mem p vt d₀ O⟩ :
          {e' : QuotEdge (↥Γ') 𝒯 // piq G Γ' e' = Quotient.mk (orbitRel G 𝒯.Dart) d₀ ∧
            qmapΓ Γ' p e' = Quotient.mk (orbitRel (↥Γ') W) vt}))
        ⟨fun O O' h => phiB_injective p vt d₀ (congrArg Subtype.val h),
         fun t => by
          obtain ⟨O, hO⟩ := phiB_surjOn p vt d₀ t.1 t.2.1 t.2.2
          exact ⟨O, Subtype.ext hO⟩⟩
        (fun O => (Γ'.subgroupOf (stabilizer G vt)).relIndex (stabilizer (↥(stabilizer G vt)) O.out))
        (fun t => nq G Γ' t.1) ?_]
    · exact OrbitCount.sum_relIndex_stabilizer_eq_index (Γ'.subgroupOf (stabilizer G vt))
        (⟨d₀, hd₀, mem_orbit_self d₀⟩ : YB p vt d₀)
        (fun y => by
          obtain ⟨g, hg⟩ := mem_orbit_iff.mp y.2.2
          have hgS : g ∈ stabilizer G vt := by
            rw [mem_stabilizer_iff, ← hd₀, ← map_smul, hg, y.2.1]
            exact hd₀.symm
          exact ⟨⟨g, hgS⟩, Subtype.ext hg⟩)
    · intro O
      show (Γ'.subgroupOf (stabilizer G vt)).relIndex (stabilizer (↥(stabilizer G vt)) O.out) = nq G Γ' (phiB Γ' p vt d₀ O)
      conv_rhs => rw [← Quotient.out_eq O, phiB_mk]
      rw [nq_mk _ (hfinD _), relIndex_YB p vt d₀ O.out (hfinD _)]
  · rw [if_neg hcase]
    have hempty : ((Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 => qmapΓ Γ' p e' = Quotient.mk (orbitRel (↥Γ') W) vt).filter
        (fun e' => piq G Γ' e' = e)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e' he' hpe
      have h2 := (Finset.mem_filter.mp he').2
      apply hcase
      rw [← hpe, piq_eq_mk_out, qmapG_mk]
      rw [← Quotient.out_eq e', qmapΓ_mk] at h2
      obtain ⟨γ, hγ⟩ := Quotient.exact h2

      exact Quotient.sound ⟨(γ : G), hγ⟩
    rw [hempty, Finset.sum_empty]

end InstB

def fstHom : 𝒯.Dart →[G] W where
  toFun d := d.fst
  map_smul' _ _ := rfl

def sndHom : 𝒯.Dart →[G] W where
  toFun d := d.snd
  map_smul' _ _ := rfl

theorem sum_nq_fibre_fst [Fintype (QuotEdge (↥Γ') 𝒯)] [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert (↥Γ') W)]
    [DecidableEq (QuotVert G W)]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    (vt : W) (e : QuotEdge G 𝒯) :
    (∑ e' ∈ (Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 =>
        (quotientDegeneracyData (↥Γ') 𝒯).a e' = Quotient.mk (orbitRel (↥Γ') W) vt).filter (fun e' => piq G Γ' e' = e), nq G Γ' e') =
      if (quotientDegeneracyData G 𝒯).a e = Quotient.mk (orbitRel G W) vt then Γ'.relIndex (stabilizer G vt) else 0 :=
  sum_nq_fibre_p (fstHom (𝒯 := 𝒯)) vt hfinV hfinD e

theorem sum_nq_fibre_snd [Fintype (QuotEdge (↥Γ') 𝒯)] [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert (↥Γ') W)]
    [DecidableEq (QuotVert G W)]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    (vt : W) (e : QuotEdge G 𝒯) :
    (∑ e' ∈ (Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 =>
        (quotientDegeneracyData (↥Γ') 𝒯).b e' = Quotient.mk (orbitRel (↥Γ') W) vt).filter (fun e' => piq G Γ' e' = e), nq G Γ' e') =
      if (quotientDegeneracyData G 𝒯).b e = Quotient.mk (orbitRel G W) vt then Γ'.relIndex (stabilizer G vt) else 0 :=
  sum_nq_fibre_p (sndHom (𝒯 := 𝒯)) vt hfinV hfinD e

variable (G Γ') in

def iota₀ : (QuotEdge G 𝒯 → ℤ) →ₗ[ℤ] (QuotEdge (↥Γ') 𝒯 → ℤ) where
  toFun x e' := (nq G Γ' e' : ℤ) * x (piq G Γ' e')
  map_add' x y := by funext e'; simp only [Pi.add_apply]; ring
  map_smul' c x := by funext e'; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem iota₀_apply (x : QuotEdge G 𝒯 → ℤ) (e' : QuotEdge (↥Γ') 𝒯) :
    iota₀ G Γ' x e' = (nq G Γ' e' : ℤ) * x (piq G Γ' e') := rfl

theorem pushforward_iota₀_eq_zero [Fintype (QuotEdge (↥Γ') 𝒯)] [Fintype (QuotEdge G 𝒯)] [DecidableEq (QuotEdge G 𝒯)]
    [DecidableEq (QuotVert G W)] [DecidableEq (QuotVert (↥Γ') W)]
    (f' : QuotEdge (↥Γ') 𝒯 → QuotVert (↥Γ') W) (f : QuotEdge G 𝒯 → QuotVert G W) (c : W → ℕ)
    (hcount : ∀ (vt : W) (e : QuotEdge G 𝒯),
      (∑ e' ∈ (Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 => f' e' = Quotient.mk (orbitRel (↥Γ') W) vt).filter
          (fun e' => piq G Γ' e' = e), nq G Γ' e') =
        if f e = Quotient.mk (orbitRel G W) vt then c vt else 0)
    (x : QuotEdge G 𝒯 → ℤ) (hx : pushforward f x = 0) :
    pushforward f' (iota₀ G Γ' x) = 0 := by
  funext v'
  have hv' : v' = Quotient.mk (orbitRel (↥Γ') W) v'.out := (Quotient.out_eq v').symm
  rw [Pi.zero_apply, pushforward_apply, ← Finset.sum_filter]
  simp only [iota₀_apply]
  rw [hv', ← Finset.sum_fiberwise _ (piq G Γ') (fun e' => (nq G Γ' e' : ℤ) * x (piq G Γ' e'))]
  have inner : ∀ e : QuotEdge G 𝒯,
      (∑ e' ∈ (Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 => f' e' = Quotient.mk (orbitRel (↥Γ') W) v'.out).filter
          (fun e' => piq G Γ' e' = e), (nq G Γ' e' : ℤ) * x (piq G Γ' e')) =
        x e * (if f e = Quotient.mk (orbitRel G W) v'.out then (c v'.out : ℤ) else 0) := by
    intro e
    have h1 : ∀ e' ∈ (Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 => f' e' = Quotient.mk (orbitRel (↥Γ') W) v'.out).filter
        (fun e' => piq G Γ' e' = e), (nq G Γ' e' : ℤ) * x (piq G Γ' e') = x e * (nq G Γ' e' : ℤ) := by
      intro e' he'
      rw [(Finset.mem_filter.mp he').2, mul_comm]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Nat.cast_sum, hcount v'.out e, Nat.cast_ite, Nat.cast_zero]
  rw [Finset.sum_congr rfl (fun e _ => inner e)]
  have h0 := congrFun hx (Quotient.mk (orbitRel G W) v'.out)
  rw [Pi.zero_apply, pushforward_apply] at h0
  have h2 : ∀ e : QuotEdge G 𝒯, x e * (if f e = Quotient.mk (orbitRel G W) v'.out then (c v'.out : ℤ) else 0) =
      (if f e = Quotient.mk (orbitRel G W) v'.out then x e else 0) * (c v'.out : ℤ) := by
    intro e
    by_cases h : f e = Quotient.mk (orbitRel G W) v'.out
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl (fun e _ => h2 e), ← Finset.sum_mul, h0, zero_mul]

theorem iota₀_mem [Fintype (QuotEdge (↥Γ') 𝒯)] [Fintype (QuotEdge G 𝒯)]
    [DecidableEq (QuotVert G W)] [DecidableEq (QuotVert (↥Γ') W)]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    (x : ↥(ribbonKernel (quotientDegeneracyData G 𝒯))) :
    iota₀ G Γ' (x : QuotEdge G 𝒯 → ℤ) ∈ ribbonKernel (quotientDegeneracyData (↥Γ') 𝒯) := by
  classical
  have hx := (mem_ribbonKernel_iff' _ _).mp x.2
  rw [mem_ribbonKernel_iff']
  exact ⟨pushforward_iota₀_eq_zero (quotientDegeneracyData (↥Γ') 𝒯).a (quotientDegeneracyData G 𝒯).a (fun vt => Γ'.relIndex (stabilizer G vt))
      (fun vt e => sum_nq_fibre_fst hfinV hfinD vt e) _ hx.1,
    pushforward_iota₀_eq_zero (quotientDegeneracyData (↥Γ') 𝒯).b (quotientDegeneracyData G 𝒯).b (fun vt => Γ'.relIndex (stabilizer G vt))
      (fun vt e => sum_nq_fibre_snd hfinV hfinD vt e) _ hx.2⟩

variable (G Γ') in

def iota [Fintype (QuotEdge (↥Γ') 𝒯)] [Fintype (QuotEdge G 𝒯)]
    [DecidableEq (QuotVert G W)] [DecidableEq (QuotVert (↥Γ') W)]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) :
    ↥(ribbonKernel (quotientDegeneracyData G 𝒯)) →ₗ[ℤ] ↥(ribbonKernel (quotientDegeneracyData (↥Γ') 𝒯)) :=
  ((iota₀ G Γ').domRestrict (ribbonKernel (quotientDegeneracyData G 𝒯))).codRestrict
    (ribbonKernel (quotientDegeneracyData (↥Γ') 𝒯)) (fun x => iota₀_mem hfinV hfinD x)

theorem coe_iota_apply [Fintype (QuotEdge (↥Γ') 𝒯)] [Fintype (QuotEdge G 𝒯)]
    [DecidableEq (QuotVert G W)] [DecidableEq (QuotVert (↥Γ') W)]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    (x : ↥(ribbonKernel (quotientDegeneracyData G 𝒯))) (e' : QuotEdge (↥Γ') 𝒯) :
    (iota G Γ' hfinV hfinD x : QuotEdge (↥Γ') 𝒯 → ℤ) e' = (nq G Γ' e' : ℤ) * (x : QuotEdge G 𝒯 → ℤ) (piq G Γ' e') := rfl

end I4a
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a"
end Mumford
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford"
end CerednikDrinfeld
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "DegeneracyData degeneracyMatrix pushforward jointDelta ribbonKernel mem_ribbonKernel"
p2m_open "CerednikDrinfeld"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "GraphAction QuotEdge QuotVert card_stabilizer_smul stabWidth stabWidth_mk quotientDegeneracyData"
p2m_open "CerednikDrinfeld.Mumford"
namespace I4a

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W} [GraphAction G 𝒯]
  {Γ' : Subgroup G} [GraphAction (↥Γ') 𝒯]

omit [GraphAction G 𝒯] [GraphAction (↥Γ') 𝒯] in

theorem card_stabilizer_smul' {H : Type} [Group H] {Y : Type} [MulAction H Y] (h : H) (y : Y) :
    Nat.card (stabilizer H (h • y)) = Nat.card (stabilizer H y) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj h).injective

theorem subgroup_smul_vert (γ : ↥Γ') (d : W) : γ • d = (γ : G) • d := rfl

theorem mem_stabilizer_subgroup_iffV (γ : ↥Γ') (d : W) :
    γ ∈ stabilizer (↥Γ') d ↔ (γ : G) ∈ stabilizer G d := Iff.rfl

theorem card_stabilizer_subgroupV (d : W) :
    Nat.card (stabilizer (↥Γ') d) = Nat.card ↥(Γ'.subgroupOf (stabilizer G d)) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨⟨(γ : ↥Γ'), (mem_stabilizer_subgroup_iffV _ d).mp γ.2⟩, by
        show ((γ : ↥Γ') : G) ∈ Γ'; exact (γ : ↥Γ').2⟩
      invFun := fun s => ⟨⟨((s : ↥(stabilizer G d)) : G), s.2⟩, by
        show (((s : ↥(stabilizer G d)) : G)) ∈ stabilizer G d; exact (s : ↥(stabilizer G d)).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_stabilizer_eq_mulV (d : W) :
    Nat.card (stabilizer G d) = Nat.card (stabilizer (↥Γ') d) * Γ'.relIndex (stabilizer G d) := by
  rw [card_stabilizer_subgroupV, Subgroup.relIndex]
  exact (Subgroup.card_mul_index (Γ'.subgroupOf (stabilizer G d))).symm

theorem relIndex_stabilizer_smulV (γ : ↥Γ') (d : W) (hfin : Finite (stabilizer G d)) :
    Γ'.relIndex (stabilizer G ((γ : G) • d)) = Γ'.relIndex (stabilizer G d) := by
  have h1 := card_stabilizer_eq_mulV (Γ' := Γ') ((γ : G) • d)
  have h2 := card_stabilizer_eq_mulV (Γ' := Γ') d
  rw [card_stabilizer_smul'] at h1
  have h3 : Nat.card (stabilizer (↥Γ') ((γ : G) • d)) = Nat.card (stabilizer (↥Γ') d) := by
    rw [← subgroup_smul_vert]; exact card_stabilizer_smul' (γ : ↥Γ') d
  rw [h3] at h1
  haveI : Finite (stabilizer (↥Γ') d) := Finite.of_injective (fun γ : stabilizer (↥Γ') d =>
    (⟨((γ : ↥Γ') : G), (mem_stabilizer_subgroup_iffV _ d).mp γ.2⟩ : stabilizer G d))
    (fun a b h => by apply Subtype.ext; apply Subtype.ext; exact congrArg (fun s : stabilizer G d => (s : G)) h)
  have hpos : 0 < Nat.card (stabilizer (↥Γ') d) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)

variable (G Γ') in

def piqV : QuotVert (↥Γ') W → QuotVert G W :=
  Quotient.map' id (fun _ _ h => by obtain ⟨γ, h⟩ := h; exact ⟨(γ : G), h⟩)

theorem piqV_mk (d : W) : piqV G Γ' (Quotient.mk (orbitRel (↥Γ') W) d) = Quotient.mk (orbitRel G W) d := rfl

theorem piqV_eq_mk_out (e' : QuotVert (↥Γ') W) :
    piqV G Γ' e' = Quotient.mk (orbitRel G W) e'.out := by
  conv_lhs => rw [← Quotient.out_eq e']
  rfl

variable (G Γ') in

def nqV (e' : QuotVert (↥Γ') W) : ℕ := Γ'.relIndex (stabilizer G e'.out)

theorem nqV_mk (d : W) (hfin : Finite (stabilizer G d)) :
    nqV G Γ' (Quotient.mk (orbitRel (↥Γ') W) d) = Γ'.relIndex (stabilizer G d) := by
  unfold nqV
  have h : (orbitRel (↥Γ') W) (Quotient.mk (orbitRel (↥Γ') W) d).out d := Quotient.mk_out d
  obtain ⟨γ, hγ⟩ := h
  change γ • d = _ at hγ
  rw [← hγ, subgroup_smul_vert]
  exact relIndex_stabilizer_smulV γ d hfin

section InstAV
variable (d₀ : W)

theorem stabilizer_orbitElemV (y : ↥(orbit G d₀)) : stabilizer G y = stabilizer G (y : W) := by
  ext g
  simp only [mem_stabilizer_iff, Subtype.ext_iff, orbit.coe_smul]

variable (Γ') in

def phiAV : orbitRel.Quotient (↥Γ') ↥(orbit G d₀) → QuotVert (↥Γ') W :=
  Quotient.map' (fun y => (y : W)) (fun a b h => by
    obtain ⟨γ, h⟩ := h
    exact ⟨γ, by rw [← h]; rfl⟩)

theorem phiAV_mk (y : ↥(orbit G d₀)) :
    phiAV Γ' d₀ (Quotient.mk (orbitRel (↥Γ') ↥(orbit G d₀)) y) = Quotient.mk (orbitRel (↥Γ') W) (y : W) := rfl

theorem piqV_phiAV (O : orbitRel.Quotient (↥Γ') ↥(orbit G d₀)) :
    piqV G Γ' (phiAV Γ' d₀ O) = Quotient.mk (orbitRel G W) d₀ := by
  induction O using Quotient.inductionOn with
  | h y =>
  rw [phiAV_mk, piqV_mk]
  exact Quotient.sound (orbitRel_apply.mpr y.2)

theorem phiAV_injective : Function.Injective (phiAV Γ' d₀) := by
  intro O O' h
  induction O using Quotient.inductionOn with
  | h y =>
  induction O' using Quotient.inductionOn with
  | h y' =>
  rw [phiAV_mk, phiAV_mk] at h
  obtain ⟨γ, hγ⟩ := Quotient.exact h
  apply Quotient.sound
  refine ⟨γ, ?_⟩
  apply Subtype.ext
  exact hγ

theorem phiAV_surjOn [DecidableEq (QuotVert G W)] (e' : QuotVert (↥Γ') W)
    (he' : piqV G Γ' e' = Quotient.mk (orbitRel G W) d₀) :
    ∃ O, phiAV Γ' d₀ O = e' := by
  have hmem : e'.out ∈ orbit G d₀ := by
    rw [piqV_eq_mk_out] at he'
    exact orbitRel_apply.mp (Quotient.exact he')
  refine ⟨Quotient.mk _ ⟨e'.out, hmem⟩, ?_⟩
  rw [phiAV_mk]
  exact Quotient.out_eq e'

end InstAV
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld"

theorem sum_nqV_fibre_eq_index [Γ'.FiniteIndex] [Fintype (QuotVert (↥Γ') W)] [DecidableEq (QuotVert G W)]
    (hfinW : ∀ d : W, Finite (stabilizer G d)) (e : QuotVert G W) :
    (∑ e' ∈ Finset.univ.filter (fun e' : QuotVert (↥Γ') W => piqV G Γ' e' = e), nqV G Γ' e') = Γ'.index := by
  classical

  have he : e = Quotient.mk (orbitRel G W) e.out := (Quotient.out_eq e).symm
  rw [he]
  haveI : Fintype (orbitRel.Quotient (↥Γ') ↥(orbit G e.out)) := Fintype.ofInjective _ (phiAV_injective e.out)
  rw [Finset.sum_subtype (Finset.univ.filter (fun e' : QuotVert (↥Γ') W => piqV G Γ' e' = Quotient.mk (orbitRel G W) e.out))
      (p := fun e' => piqV G Γ' e' = Quotient.mk (orbitRel G W) e.out) (fun e' => by simp)]
  rw [← Fintype.sum_bijective (fun O => (⟨phiAV Γ' e.out O, piqV_phiAV e.out O⟩ :
        {e' : QuotVert (↥Γ') W // piqV G Γ' e' = Quotient.mk (orbitRel G W) e.out}))
      ⟨fun O O' h => phiAV_injective e.out (congrArg Subtype.val h),
       fun t => by
        obtain ⟨O, hO⟩ := phiAV_surjOn e.out t.1 t.2
        exact ⟨O, Subtype.ext hO⟩⟩
      (fun O => Γ'.relIndex (stabilizer G O.out)) (fun t => nqV G Γ' t.1) ?_]
  · exact OrbitCount.sum_relIndex_stabilizer_eq_index Γ' ⟨e.out, mem_orbit_self e.out⟩
      (fun y => by
        obtain ⟨g, hg⟩ := mem_orbit_iff.mp y.2
        exact ⟨g, Subtype.ext hg⟩)
  · intro O
    show Γ'.relIndex (stabilizer G O.out) = nqV G Γ' (phiAV Γ' e.out O)
    conv_rhs => rw [← Quotient.out_eq O, phiAV_mk]
    rw [nqV_mk _ (hfinW _), stabilizer_orbitElemV]

end I4a
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld"
end Mumford
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld"
end CerednikDrinfeld
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford.I4a P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.CerednikDrinfeld"

open CerednikDrinfeld.Mumford.I4a in
theorem solution
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (Γ' : Subgroup G) [GraphAction (↥Γ') 𝒯] [Γ'.FiniteIndex]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    [Fintype (QuotEdge G 𝒯)] [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert G W)]
    [Fintype (QuotEdge (↥Γ') 𝒯)] [Fintype (QuotVert (↥Γ') W)] [DecidableEq (QuotVert (↥Γ') W)] :
    ∃ μ : (quotientDegeneracyData (↥Γ') 𝒯).FiniteHom (quotientDegeneracyData G 𝒯),
      (∀ e' : QuotEdge (↥Γ') 𝒯, μ.mapE e' = Quotient.mk (orbitRel G 𝒯.Dart) e'.out) ∧
      (∀ v' : QuotVert (↥Γ') W, μ.mapV v' = Quotient.mk (orbitRel G W) v'.out) ∧
      (∀ e' : QuotEdge (↥Γ') 𝒯,
        (μ.deg e' : ℕ) * Nat.card (stabilizer (↥Γ') e'.out) = Nat.card (stabilizer G e'.out)) ∧
      (∀ v' : QuotVert (↥Γ') W,
        (μ.degV v' : ℕ) * Nat.card (stabilizer (↥Γ') v'.out) = Nat.card (stabilizer G v'.out)) ∧
      (μ.degTotal : ℕ) = Γ'.index := by
  classical

  have hposE : ∀ e' : QuotEdge (↥Γ') 𝒯, 0 < nq G Γ' e' := by
    intro e'
    haveI := hfinD e'.out
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Γ'.subgroupOf (stabilizer G e'.out)))
  have hposV : ∀ v' : QuotVert (↥Γ') W, 0 < nqV G Γ' v' := by
    intro v'
    haveI := hfinV v'.out
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Γ'.subgroupOf (stabilizer G v'.out)))
  have hposT : 0 < Γ'.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

  have ha : ∀ e' : QuotEdge (↥Γ') 𝒯,
      (quotientDegeneracyData G 𝒯).a (piq G Γ' e') = piqV G Γ' ((quotientDegeneracyData (↥Γ') 𝒯).a e') := by
    intro e'
    induction e' using Quotient.inductionOn with
    | h d => rfl
  have hb : ∀ e' : QuotEdge (↥Γ') 𝒯,
      (quotientDegeneracyData G 𝒯).b (piq G Γ' e') = piqV G Γ' ((quotientDegeneracyData (↥Γ') 𝒯).b e') := by
    intro e'
    induction e' using Quotient.inductionOn with
    | h d => rfl

  have harm : ∀ (v : QuotVert (↥Γ') W) (e : QuotEdge G 𝒯)
      (c₁ : QuotEdge (↥Γ') 𝒯 → QuotVert (↥Γ') W) (c₂ : QuotEdge G 𝒯 → QuotVert G W),
      (∀ (vt : W) (e : QuotEdge G 𝒯),
        (∑ e' ∈ (Finset.univ.filter fun e' : QuotEdge (↥Γ') 𝒯 => c₁ e' = Quotient.mk (orbitRel (↥Γ') W) vt).filter
            (fun e' => piq G Γ' e' = e), nq G Γ' e') =
          if c₂ e = Quotient.mk (orbitRel G W) vt then Γ'.relIndex (stabilizer G vt) else 0) →
      c₂ e = piqV G Γ' v →
      (∑ e' ∈ Finset.univ.filter (fun e' : QuotEdge (↥Γ') 𝒯 => c₁ e' = v ∧ piq G Γ' e' = e), nq G Γ' e') =
        nqV G Γ' v := by
    intro v e c₁ c₂ hcount hv
    have h := hcount v.out e
    rw [Finset.filter_filter, Quotient.out_eq v] at h
    rw [h, if_pos (hv.trans (piqV_eq_mk_out v))]
    rfl
  refine ⟨{ mapV := piqV G Γ'
            mapE := piq G Γ'
            a_mapE := ha
            b_mapE := hb
            deg := fun e' => ⟨nq G Γ' e', hposE e'⟩
            degV := fun v' => ⟨nqV G Γ' v', hposV v'⟩
            degTotal := ⟨Γ'.index, hposT⟩
            w_mapE := fun e' => ?_
            sum_deg_a := fun v e h => ?_
            sum_deg_b := fun v e h => ?_
            sum_degV := fun v => ?_ }, fun e' => piq_eq_mk_out e', fun v' => piqV_eq_mk_out v', fun e' => ?_, fun v' => ?_, rfl⟩
  ·
    apply PNat.eq
    rw [PNat.mul_coe, PNat.mk_coe, piq_eq_mk_out, mul_comm]
    exact width_eq_mul e' (hfinD _)
  ·
    exact harm v e _ _ (fun vt e => sum_nq_fibre_fst hfinV hfinD vt e) h
  ·
    exact harm v e _ _ (fun vt e => sum_nq_fibre_snd hfinV hfinD vt e) h
  ·
    exact sum_nqV_fibre_eq_index hfinV v
  ·
    show nq G Γ' e' * _ = _
    rw [nq, mul_comm]
    exact (card_stabilizer_eq_mul e'.out).symm
  ·
    show nqV G Γ' v' * _ = _
    rw [nqV, mul_comm]
    exact (card_stabilizer_eq_mulV v'.out).symm

end
end S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup (solution)
