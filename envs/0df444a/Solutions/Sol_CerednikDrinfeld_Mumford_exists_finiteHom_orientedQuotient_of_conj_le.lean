-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_finiteHom_orientedQuotient_of_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c4d66c54-f715-5631-b71f-c9876a438984

import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_orientedQuotient_of_conj_le

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem solution
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W)
    (X Y : Subgroup G) (hX : X ≤ typePreserving G 𝒯 w₀) (hY : Y ≤ typePreserving G 𝒯 w₀)
    (g : G) (hg : g ∈ typePreserving G 𝒯 w₀)
    (hXY : ∀ x ∈ X, g⁻¹ * x * g ∈ Y)
    (hidx : (X.map (MulAut.conj g⁻¹).toMonoidHom).relIndex Y ≠ 0)
    (hfinV : ∀ v : W, Finite (stabilizer (↥Y) v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer (↥Y) d))

    {E V E' V' : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
    [Fintype E'] [DecidableEq E'] [Fintype V'] [DecidableEq V']
    (D : DegeneracyData E V) (eV : QuotVert (↥X) W ≃ V) (eE : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (orbitRel (↥X) W) e.1.out.fst))
    (hDb : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (orbitRel (↥X) W) e.1.out.snd))
    (hDw : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (stabilizer (↥X) e.1.out))
    (D' : DegeneracyData E' V') (eV' : QuotVert (↥Y) W ≃ V') (eE' : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} ≃ E')
    (hDa' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D'.a (eE' e) = eV' (Quotient.mk (orbitRel (↥Y) W) e.1.out.fst))
    (hDb' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D'.b (eE' e) = eV' (Quotient.mk (orbitRel (↥Y) W) e.1.out.snd))
    (hDw' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, (D'.w (eE' e) : ℕ) = Nat.card (stabilizer (↥Y) e.1.out)) :
    ∃ μ : D.FiniteHom D',
      (∀ v : W, μ.mapV (eV (Quotient.mk (orbitRel (↥X) W) v)) = eV' (Quotient.mk (orbitRel (↥Y) W) (g⁻¹ • v))) ∧
      (∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0},
        ((eE'.symm (μ.mapE (eE e))) : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}).1 = Quotient.mk (orbitRel (↥Y) 𝒯.Dart) (g⁻¹ • e.1.out)) ∧
      (μ.degTotal : ℕ) = (X.map (MulAut.conj g⁻¹).toMonoidHom).relIndex Y := by
  classical

  have htpY : ∀ (y : ↥Y) (w : W), vertexType 𝒯 w₀ ((y : G) • w) = vertexType 𝒯 w₀ w := fun y w => hY y.2 w
  have htpX : ∀ (x : ↥X) (w : W), vertexType 𝒯 w₀ ((x : G) • w) = vertexType 𝒯 w₀ w := fun x w => hX x.2 w
  have htpg : ∀ w : W, vertexType 𝒯 w₀ (g⁻¹ • w) = vertexType 𝒯 w₀ w := fun w => (typePreserving G 𝒯 w₀).inv_mem hg w
  have htpg' : ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w := fun w => hg w

  let X' : Subgroup ↥Y := (X.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf Y

  let cj : ↥X → ↥X' := fun x => ⟨⟨g⁻¹ * x * g, hXY x x.2⟩, by
    change ((⟨g⁻¹ * x * g, hXY x x.2⟩ : ↥Y) : G) ∈ X.map (MulAut.conj g⁻¹).toMonoidHom
    exact ⟨x, x.2, by simp [MulAut.conj_apply, mul_assoc]⟩⟩
  have hcj : ∀ x : ↥X, (((cj x : ↥X') : ↥Y) : G) = g⁻¹ * x * g := fun x => rfl
  have hX'elim : ∀ z : ↥X', ∃ x : ↥X, cj x = z := by
    intro z
    obtain ⟨x, hx, hxz⟩ := (Subgroup.mem_subgroupOf.mp z.2)
    refine ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext ?_)⟩
    simpa [hcj, MulAut.conj_apply, mul_assoc] using hxz

  have hsmulX' : ∀ (z : ↥X') (w : W), z • w = ((z : ↥Y) : G) • w := fun z w => rfl
  have hsmulX'd : ∀ (z : ↥X') (d : 𝒯.Dart), z • d = ((z : ↥Y) : G) • d := fun z d => rfl
  have hsmulY : ∀ (y : ↥Y) (w : W), y • w = (y : G) • w := fun y w => rfl
  have hsmulYd : ∀ (y : ↥Y) (d : 𝒯.Dart), y • d = (y : G) • d := fun y d => rfl
  have hsmulX : ∀ (x : ↥X) (w : W), x • w = (x : G) • w := fun x w => rfl
  have hsmulXd : ∀ (x : ↥X) (d : 𝒯.Dart), x • d = (x : G) • d := fun x d => rfl

  have hconjV : ∀ (x : ↥X) (w : W), g⁻¹ • ((x : G) • w) = (cj x) • (g⁻¹ • w) := by
    intro x w; rw [hsmulX', hcj, ← mul_smul, ← mul_smul]; congr 1; group
  have hconjD : ∀ (x : ↥X) (d : 𝒯.Dart), g⁻¹ • ((x : G) • d) = (cj x) • (g⁻¹ • d) := by
    intro x d; rw [hsmulX'd, hcj, ← mul_smul, ← mul_smul]; congr 1; group
  have hconjV' : ∀ (x : ↥X) (w : W), g • ((cj x) • w) = (x : G) • (g • w) := by
    intro x w; rw [hsmulX', hcj, ← mul_smul, ← mul_smul]; congr 1; group
  have hconjD' : ∀ (x : ↥X) (d : 𝒯.Dart), g • ((cj x) • d) = (x : G) • (g • d) := by
    intro x d; rw [hsmulX'd, hcj, ← mul_smul, ← mul_smul]; congr 1; group

  let cV : QuotVert (↥X) W ≃ QuotVert (↥X') W :=
    { toFun := Quotient.map' (fun w : W => g⁻¹ • w) (by
        rintro a b ⟨x, rfl⟩; exact ⟨cj x, show (cj x) • (g⁻¹ • b) = g⁻¹ • (x • b) by rw [hsmulX]; exact (hconjV x b).symm⟩)
      invFun := Quotient.map' (fun w : W => g • w) (by
        rintro a b ⟨z, rfl⟩; obtain ⟨x, rfl⟩ := hX'elim z; exact ⟨x, show x • (g • b) = g • ((cj x) • b) by rw [hsmulX]; exact (hconjV' x b).symm⟩)
      left_inv := by rintro ⟨w⟩; exact congrArg (Quotient.mk _) (smul_inv_smul g w)
      right_inv := by rintro ⟨w⟩; exact congrArg (Quotient.mk _) (inv_smul_smul g w) }
  have hcV : ∀ w : W, cV (Quotient.mk (orbitRel (↥X) W) w) = Quotient.mk (orbitRel (↥X') W) (g⁻¹ • w) := fun w => rfl
  have hcVs : ∀ w : W, cV.symm (Quotient.mk (orbitRel (↥X') W) w) = Quotient.mk (orbitRel (↥X) W) (g • w) := fun w => rfl
  let cD : QuotEdge (↥X) 𝒯 ≃ QuotEdge (↥X') 𝒯 :=
    { toFun := Quotient.map' (fun d : 𝒯.Dart => g⁻¹ • d) (by
        rintro a b ⟨x, rfl⟩; exact ⟨cj x, show (cj x) • (g⁻¹ • b) = g⁻¹ • (x • b) by rw [hsmulXd]; exact (hconjD x b).symm⟩)
      invFun := Quotient.map' (fun d : 𝒯.Dart => g • d) (by
        rintro a b ⟨z, rfl⟩; obtain ⟨x, rfl⟩ := hX'elim z; exact ⟨x, show x • (g • b) = g • ((cj x) • b) by rw [hsmulXd]; exact (hconjD' x b).symm⟩)
      left_inv := by rintro ⟨d⟩; exact congrArg (Quotient.mk _) (smul_inv_smul g d)
      right_inv := by rintro ⟨d⟩; exact congrArg (Quotient.mk _) (inv_smul_smul g d) }
  have hcD : ∀ d : 𝒯.Dart, cD (Quotient.mk (orbitRel (↥X) 𝒯.Dart) d) = Quotient.mk (orbitRel (↥X') 𝒯.Dart) (g⁻¹ • d) := fun d => rfl
  have hcDs : ∀ d : 𝒯.Dart, cD.symm (Quotient.mk (orbitRel (↥X') 𝒯.Dart) d) = Quotient.mk (orbitRel (↥X) 𝒯.Dart) (g • d) := fun d => rfl

  obtain ⟨hadj, -, -⟩ :=
    CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter G 𝒯 hc hb w₀
  have h01 : ∀ t : ZMod 2, t ≠ 0 → t + 1 = 0 := by decide

  have horY : ∀ d : 𝒯.Dart, vertexType 𝒯 w₀ (Quotient.mk (orbitRel (↥Y) 𝒯.Dart) d).out.fst = vertexType 𝒯 w₀ d.fst := by
    intro d
    obtain ⟨y, hy⟩ := Quotient.mk_out (s := orbitRel (↥Y) 𝒯.Dart) d
    rw [← hy]; exact htpY y d.fst
  have horX : ∀ d : 𝒯.Dart, vertexType 𝒯 w₀ (Quotient.mk (orbitRel (↥X) 𝒯.Dart) d).out.fst = vertexType 𝒯 w₀ d.fst := by
    intro d
    obtain ⟨x, hx⟩ := Quotient.mk_out (s := orbitRel (↥X) 𝒯.Dart) d
    rw [← hx]; exact htpX x d.fst
  have horX' : ∀ d : 𝒯.Dart, vertexType 𝒯 w₀ (Quotient.mk (orbitRel (↥X') 𝒯.Dart) d).out.fst = vertexType 𝒯 w₀ d.fst := by
    intro d
    obtain ⟨z, hz⟩ := Quotient.mk_out (s := orbitRel (↥X') 𝒯.Dart) d
    rw [← hz]; exact htpY z d.fst
  have horYV : ∀ w : W, vertexType 𝒯 w₀ (Quotient.mk (orbitRel (↥Y) W) w).out = vertexType 𝒯 w₀ w := by
    intro w
    obtain ⟨y, hy⟩ := Quotient.mk_out (s := orbitRel (↥Y) W) w
    rw [← hy]; exact htpY y w

  have hfinQ : ∀ (H : Subgroup G), H ≤ typePreserving G 𝒯 w₀ →
      Finite {e : QuotEdge (↥H) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} → Finite (QuotEdge (↥H) 𝒯) := by
    intro H hH hF
    have htpH : ∀ (h : ↥H) (w : W), vertexType 𝒯 w₀ ((h : G) • w) = vertexType 𝒯 w₀ w := fun h w => hH h.2 w
    have horH : ∀ d : 𝒯.Dart, vertexType 𝒯 w₀ (Quotient.mk (orbitRel (↥H) 𝒯.Dart) d).out.fst = vertexType 𝒯 w₀ d.fst := by
      intro d
      obtain ⟨h, hh⟩ := Quotient.mk_out (s := orbitRel (↥H) 𝒯.Dart) d
      rw [← hh]; exact htpH h d.fst
    let f : {e : QuotEdge (↥H) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} ⊕ {e : QuotEdge (↥H) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} →
        QuotEdge (↥H) 𝒯 := fun s => match s with
      | Sum.inl e => e.1
      | Sum.inr e => quotientReversal (↥H) 𝒯 e.1
    refine Finite.of_surjective f ?_
    intro c
    induction c using Quotient.ind with
    | _ d =>
      by_cases h0 : vertexType 𝒯 w₀ d.fst = 0
      · exact ⟨Sum.inl ⟨Quotient.mk _ d, by rw [horH]; exact h0⟩, rfl⟩
      · refine ⟨Sum.inr ⟨Quotient.mk _ d.symm, ?_⟩, ?_⟩
        · rw [horH]; show vertexType 𝒯 w₀ d.snd = 0
          rw [hadj d.fst d.snd d.adj]; exact h01 _ h0
        · show Quotient.mk _ d.symm.symm = Quotient.mk _ d
          rw [SimpleGraph.Dart.symm_symm]
  haveI : Finite (QuotEdge (↥Y) 𝒯) := hfinQ Y hY (Finite.of_equiv _ eE'.symm)
  haveI : Fintype (QuotEdge (↥Y) 𝒯) := Fintype.ofFinite _
  haveI : Finite (QuotEdge (↥X) 𝒯) := hfinQ X hX (Finite.of_equiv _ eE.symm)
  haveI : Fintype (QuotEdge (↥X') 𝒯) := @Fintype.ofFinite _ (Finite.of_equiv _ cD)
  haveI : Fintype (QuotVert (↥X') W) := @Fintype.ofFinite _ (Finite.of_equiv _ (eV.symm.trans cV))
  haveI : X'.FiniteIndex := ⟨hidx⟩
  have hfinV' : ∀ v : W, Finite (stabilizer (↥Y) v) := hfinV
  have hfinD' : ∀ d : 𝒯.Dart, Finite (stabilizer (↥Y) d) := hfinD
  obtain ⟨μ₀, hμE, hμV, hμdeg, hμdegV, hμtot⟩ :=
    CerednikDrinfeld.Mumford.exists_finiteHom_quotientDegeneracyData_of_subgroup (↥Y) 𝒯 X' hfinV' hfinD'

  have hcj_inj : Function.Injective cj := by
    intro x₁ x₂ h
    have h' : g⁻¹ * (x₁ : G) * g = g⁻¹ * x₂ * g := by
      have := congrArg (fun z : ↥X' => ((z : ↥Y) : G)) h; simpa [hcj] using this
    exact Subtype.ext (by simpa [mul_assoc] using h')
  let cjE : ↥X ≃ ↥X' := Equiv.ofBijective cj ⟨hcj_inj, fun z => hX'elim z⟩

  have hstabX : ∀ d : 𝒯.Dart, Nat.card (stabilizer (↥X') (g⁻¹ • d)) = Nat.card (stabilizer (↥X) d) := by
    intro d
    refine (Nat.card_congr ?_).symm
    refine { toFun := fun x => ⟨cj x.1, ?_⟩, invFun := fun z => ⟨cjE.symm z.1, ?_⟩, left_inv := ?_, right_inv := ?_ }
    · show (cj x.1) • (g⁻¹ • d) = g⁻¹ • d
      rw [← hconjD, show ((x.1 : ↥X) : G) • d = d from x.2]
    · show ((cjE.symm z.1 : ↥X) : G) • d = d
      have hz : (cj (cjE.symm z.1)) • (g⁻¹ • d) = g⁻¹ • d := by
        rw [show cj (cjE.symm z.1) = z.1 from cjE.apply_symm_apply z.1]; exact z.2
      rw [← hconjD] at hz
      simpa using congrArg (fun e => g • e) hz
    · intro x; exact Subtype.ext (cjE.symm_apply_apply x.1)
    · intro z; exact Subtype.ext (cjE.apply_symm_apply z.1)

  have houtD : ∀ d : 𝒯.Dart, Quotient.mk (orbitRel (↥Y) 𝒯.Dart) (Quotient.mk (orbitRel (↥X') 𝒯.Dart) d).out =
      Quotient.mk (orbitRel (↥Y) 𝒯.Dart) d := by
    intro d
    obtain ⟨z, hz⟩ := Quotient.mk_out (s := orbitRel (↥X') 𝒯.Dart) d
    rw [← hz]; exact Quotient.sound ⟨(z : ↥Y), rfl⟩
  have houtV : ∀ w : W, Quotient.mk (orbitRel (↥Y) W) (Quotient.mk (orbitRel (↥X') W) w).out =
      Quotient.mk (orbitRel (↥Y) W) w := by
    intro w
    obtain ⟨z, hz⟩ := Quotient.mk_out (s := orbitRel (↥X') W) w
    rw [← hz]; exact Quotient.sound ⟨(z : ↥Y), rfl⟩
  have houtXV : ∀ w : W, Quotient.mk (orbitRel (↥Y) W) (g⁻¹ • (Quotient.mk (orbitRel (↥X) W) w).out) =
      Quotient.mk (orbitRel (↥Y) W) (g⁻¹ • w) := by
    intro w
    obtain ⟨x, hx⟩ := Quotient.mk_out (s := orbitRel (↥X) W) w
    rw [← hx]
    show Quotient.mk (orbitRel (↥Y) W) (g⁻¹ • ((x : G) • w)) = _
    rw [hconjV]; exact Quotient.sound ⟨((cj x : ↥X') : ↥Y), rfl⟩
  have houtXD : ∀ d : 𝒯.Dart, Quotient.mk (orbitRel (↥Y) 𝒯.Dart) (g⁻¹ • (Quotient.mk (orbitRel (↥X) 𝒯.Dart) d).out) =
      Quotient.mk (orbitRel (↥Y) 𝒯.Dart) (g⁻¹ • d) := by
    intro d
    obtain ⟨x, hx⟩ := Quotient.mk_out (s := orbitRel (↥X) 𝒯.Dart) d
    rw [← hx]
    show Quotient.mk (orbitRel (↥Y) 𝒯.Dart) (g⁻¹ • ((x : G) • d)) = _
    rw [hconjD]; exact Quotient.sound ⟨((cj x : ↥X') : ↥Y), rfl⟩

  have hME : ∀ q : QuotEdge (↥X) 𝒯, μ₀.mapE (cD q) = Quotient.mk (orbitRel (↥Y) 𝒯.Dart) (g⁻¹ • q.out) := by
    intro q
    conv_lhs => rw [← Quotient.out_eq q]
    rw [hcD, hμE, houtD]
  have hMV : ∀ q : QuotVert (↥X) W, μ₀.mapV (cV q) = Quotient.mk (orbitRel (↥Y) W) (g⁻¹ • q.out) := by
    intro q
    conv_lhs => rw [← Quotient.out_eq q]
    rw [hcV, hμV, houtV]

  have horE : ∀ eo : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, vertexType 𝒯 w₀ (μ₀.mapE (cD eo.1)).out.fst = 0 := by
    intro eo
    rw [hME, horY]
    show vertexType 𝒯 w₀ (g⁻¹ • eo.1.out.fst) = 0
    rw [htpg]; exact eo.2

  have haY : ∀ d : 𝒯.Dart, (quotientDegeneracyData (↥Y) 𝒯).a (Quotient.mk _ d) = Quotient.mk (orbitRel (↥Y) W) d.fst := fun d => rfl
  have hbY : ∀ d : 𝒯.Dart, (quotientDegeneracyData (↥Y) 𝒯).b (Quotient.mk _ d) = Quotient.mk (orbitRel (↥Y) W) d.snd := fun d => rfl
  have haX' : ∀ d : 𝒯.Dart, (quotientDegeneracyData (↥X') 𝒯).a (Quotient.mk _ d) = Quotient.mk (orbitRel (↥X') W) d.fst := fun d => rfl
  have hbX' : ∀ d : 𝒯.Dart, (quotientDegeneracyData (↥X') 𝒯).b (Quotient.mk _ d) = Quotient.mk (orbitRel (↥X') W) d.snd := fun d => rfl
  have haY' : ∀ c : QuotEdge (↥Y) 𝒯, Quotient.mk (orbitRel (↥Y) W) c.out.fst = (quotientDegeneracyData (↥Y) 𝒯).a c := by
    intro c; conv_rhs => rw [← Quotient.out_eq c]
    rfl
  have hbY' : ∀ c : QuotEdge (↥Y) 𝒯, Quotient.mk (orbitRel (↥Y) W) c.out.snd = (quotientDegeneracyData (↥Y) 𝒯).b c := by
    intro c; conv_rhs => rw [← Quotient.out_eq c]
    rfl
  have haXc : ∀ q : QuotEdge (↥X) 𝒯, (quotientDegeneracyData (↥X') 𝒯).a (cD q) = cV (Quotient.mk (orbitRel (↥X) W) q.out.fst) := by
    intro q; conv_lhs => rw [← Quotient.out_eq q]
    rw [hcD, haX', hcV]; rfl
  have hbXc : ∀ q : QuotEdge (↥X) 𝒯, (quotientDegeneracyData (↥X') 𝒯).b (cD q) = cV (Quotient.mk (orbitRel (↥X) W) q.out.snd) := by
    intro q; conv_lhs => rw [← Quotient.out_eq q]
    rw [hcD, hbX', hcV]; rfl

  have hstab_outY : ∀ d : 𝒯.Dart, Nat.card (stabilizer (↥Y) (Quotient.mk (orbitRel (↥Y) 𝒯.Dart) d).out) = Nat.card (stabilizer (↥Y) d) := by
    intro d
    obtain ⟨y, hy⟩ := Quotient.mk_out (s := orbitRel (↥Y) 𝒯.Dart) d
    rw [← hy]; exact card_stabilizer_smul 𝒯 y d
  have hstab_outX' : ∀ d : 𝒯.Dart, Nat.card (stabilizer (↥X') (Quotient.mk (orbitRel (↥X') 𝒯.Dart) d).out) = Nat.card (stabilizer (↥X') d) := by
    intro d
    obtain ⟨z, hz⟩ := Quotient.mk_out (s := orbitRel (↥X') 𝒯.Dart) d
    rw [← hz]; exact card_stabilizer_smul 𝒯 z d
  have hstab_outX'Y : ∀ d : 𝒯.Dart, Nat.card (stabilizer (↥Y) (Quotient.mk (orbitRel (↥X') 𝒯.Dart) d).out) = Nat.card (stabilizer (↥Y) d) := by
    intro d
    obtain ⟨z, hz⟩ := Quotient.mk_out (s := orbitRel (↥X') 𝒯.Dart) d
    rw [← hz]; exact card_stabilizer_smul 𝒯 (z : ↥Y) d

  have hdegrep : ∀ d : 𝒯.Dart, (μ₀.deg (cD (Quotient.mk _ d)) : ℕ) * Nat.card (stabilizer (↥X) d) = Nat.card (stabilizer (↥Y) (g⁻¹ • d)) := by
    intro d
    have h := hμdeg (cD (Quotient.mk _ d))
    rw [hcD, hstab_outX', hstab_outX'Y, hstabX] at h
    rw [hcD]; exact h
  have hdegrep' : ∀ q : QuotEdge (↥X) 𝒯, (μ₀.deg (cD q) : ℕ) * Nat.card (stabilizer (↥X) q.out) = Nat.card (stabilizer (↥Y) (g⁻¹ • q.out)) := by
    intro q
    have h := hdegrep q.out
    rwa [Quotient.out_eq] at h
  have hfstY : ∀ (c : QuotEdge (↥Y) 𝒯) (d : 𝒯.Dart), c = Quotient.mk _ d →
      Quotient.mk (orbitRel (↥Y) W) c.out.fst = Quotient.mk (orbitRel (↥Y) W) d.fst := by
    intro c d h; rw [haY', h, haY]
  have hsndY : ∀ (c : QuotEdge (↥Y) 𝒯) (d : 𝒯.Dart), c = Quotient.mk _ d →
      Quotient.mk (orbitRel (↥Y) W) c.out.snd = Quotient.mk (orbitRel (↥Y) W) d.snd := by
    intro c d h; rw [hbY', h, hbY]
  have hstabYc : ∀ (c : QuotEdge (↥Y) 𝒯) (d : 𝒯.Dart), c = Quotient.mk _ d →
      Nat.card (stabilizer (↥Y) c.out) = Nat.card (stabilizer (↥Y) d) := by
    intro c d h; rw [h, hstab_outY]

  let ι : E → QuotEdge (↥X') 𝒯 := fun e => cD (eE.symm e).1
  let κ : V → QuotVert (↥X') W := fun v => cV (eV.symm v)
  have hιinj : Function.Injective ι := fun e₁ e₂ h => eE.symm.injective (Subtype.ext (cD.injective h))
  have hκinj : Function.Injective κ := fun v₁ v₂ h => eV.symm.injective (cV.injective h)

  have hA : ∀ eo : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0},
      D'.a (eE' ⟨μ₀.mapE (cD eo.1), horE eo⟩) = eV' (μ₀.mapV (cV (eV.symm (D.a (eE eo))))) := by
    intro eo
    rw [hDa eo, Equiv.symm_apply_apply, hMV, houtXV, hDa' ⟨μ₀.mapE (cD eo.1), horE eo⟩]
    show eV' (Quotient.mk _ (μ₀.mapE (cD eo.1)).out.fst) = eV' (Quotient.mk _ (g⁻¹ • eo.1.out.fst))
    rw [hfstY (μ₀.mapE (cD eo.1)) (g⁻¹ • eo.1.out) (hME eo.1)]
    rfl
  have hB : ∀ eo : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0},
      D'.b (eE' ⟨μ₀.mapE (cD eo.1), horE eo⟩) = eV' (μ₀.mapV (cV (eV.symm (D.b (eE eo))))) := by
    intro eo
    rw [hDb eo, Equiv.symm_apply_apply, hMV, houtXV, hDb' ⟨μ₀.mapE (cD eo.1), horE eo⟩]
    show eV' (Quotient.mk _ (μ₀.mapE (cD eo.1)).out.snd) = eV' (Quotient.mk _ (g⁻¹ • eo.1.out.snd))
    rw [hsndY (μ₀.mapE (cD eo.1)) (g⁻¹ • eo.1.out) (hME eo.1)]
    rfl
  have hWl : ∀ eo : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0},
      (D'.w (eE' ⟨μ₀.mapE (cD eo.1), horE eo⟩) : ℕ) = μ₀.deg (cD eo.1) * (D.w (eE eo) : ℕ) := by
    intro eo
    rw [hDw' ⟨μ₀.mapE (cD eo.1), horE eo⟩, hDw eo]
    show Nat.card (stabilizer (↥Y) (μ₀.mapE (cD eo.1)).out) = _
    rw [hstabYc (μ₀.mapE (cD eo.1)) (g⁻¹ • eo.1.out) (hME eo.1)]
    exact (hdegrep' eo.1).symm

  have hA' : ∀ e : E, D'.a (eE' ⟨μ₀.mapE (cD (eE.symm e).1), horE (eE.symm e)⟩) = eV' (μ₀.mapV (cV (eV.symm (D.a e)))) := by
    intro e; have h := hA (eE.symm e); rwa [Equiv.apply_symm_apply] at h
  have hB' : ∀ e : E, D'.b (eE' ⟨μ₀.mapE (cD (eE.symm e).1), horE (eE.symm e)⟩) = eV' (μ₀.mapV (cV (eV.symm (D.b e)))) := by
    intro e; have h := hB (eE.symm e); rwa [Equiv.apply_symm_apply] at h
  have hWl' : ∀ e : E, (D'.w (eE' ⟨μ₀.mapE (cD (eE.symm e).1), horE (eE.symm e)⟩) : ℕ) = μ₀.deg (cD (eE.symm e).1) * (D.w e : ℕ) := by
    intro e; have h := hWl (eE.symm e); rwa [Equiv.apply_symm_apply] at h

  have hlift : ∀ (b : QuotEdge (↥X') 𝒯) (c : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}), μ₀.mapE b = c.1 → vertexType 𝒯 w₀ (cD.symm b).out.fst = 0 := by
    intro b c hbc
    have h1 : vertexType 𝒯 w₀ b.out.fst = 0 := by
      have h2 := c.2
      rw [← hbc, hμE, horY] at h2; exact h2
    have h3 : cD.symm b = Quotient.mk (orbitRel (↥X) 𝒯.Dart) (g • b.out) := by
      conv_lhs => rw [← Quotient.out_eq b]
      rfl
    rw [h3, horX]
    show vertexType 𝒯 w₀ (g • b.out.fst) = 0
    rw [htpg']; exact h1

  refine ⟨{ mapV := fun v => eV' (μ₀.mapV (κ v))
            mapE := fun e => eE' ⟨μ₀.mapE (ι e), horE (eE.symm e)⟩
            a_mapE := fun e => hA' e
            b_mapE := fun e => hB' e
            deg := fun e => μ₀.deg (ι e)
            degV := fun v => μ₀.degV (κ v)
            degTotal := μ₀.degTotal
            w_mapE := ?_
            sum_deg_a := ?_
            sum_deg_b := ?_
            sum_degV := ?_ }, ?_, ?_, ?_⟩
  ·
    intro e; apply PNat.eq; rw [PNat.mul_coe]; exact hWl' e
  ·
    intro v e' hve'
    have hv₀ : (quotientDegeneracyData (↥Y) 𝒯).a (eE'.symm e').1 = μ₀.mapV (κ v) := by
      apply eV'.injective
      have h := hDa' (eE'.symm e'); rw [Equiv.apply_symm_apply] at h
      rw [← haY', ← h]; exact hve'
    rw [← μ₀.sum_deg_a (κ v) (eE'.symm e').1 hv₀]
    refine Finset.sum_bij (fun e _ => ι e) ?_ ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [haXc]
        show cV _ = cV (eV.symm v)
        congr 1; apply eV.injective
        rw [Equiv.apply_symm_apply, ← hDa (eE.symm e), Equiv.apply_symm_apply]; exact he.2.1
      · have h := congrArg (fun t => (eE'.symm t).1) he.2.2
        simpa using h
    · intro e₁ _ e₂ _ h; exact hιinj h
    · intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨-, hb1, hb2⟩ := hb
      have hbt := hlift b (eE'.symm e') hb2
      refine ⟨eE ⟨cD.symm b, hbt⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · have h2 : cV (Quotient.mk (orbitRel (↥X) W) (cD.symm b).out.fst) = cV (eV.symm v) := by
            rw [← haXc (cD.symm b), Equiv.apply_symm_apply]; exact hb1
          rw [hDa, cV.injective h2, Equiv.apply_symm_apply]
        · apply eE'.symm.injective; apply Subtype.ext
          rw [Equiv.symm_apply_apply]
          show μ₀.mapE (cD (eE.symm (eE ⟨cD.symm b, hbt⟩)).1) = (eE'.symm e').1
          rw [Equiv.symm_apply_apply]
          show μ₀.mapE (cD (cD.symm b)) = _
          rw [Equiv.apply_symm_apply]; exact hb2
      · show cD (eE.symm (eE ⟨cD.symm b, hbt⟩)).1 = b
        rw [Equiv.symm_apply_apply]; exact cD.apply_symm_apply b
    · intro e _; rfl
  ·
    intro v e' hve'
    have hv₀ : (quotientDegeneracyData (↥Y) 𝒯).b (eE'.symm e').1 = μ₀.mapV (κ v) := by
      apply eV'.injective
      have h := hDb' (eE'.symm e'); rw [Equiv.apply_symm_apply] at h
      rw [← hbY', ← h]; exact hve'
    rw [← μ₀.sum_deg_b (κ v) (eE'.symm e').1 hv₀]
    refine Finset.sum_bij (fun e _ => ι e) ?_ ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [hbXc]
        show cV _ = cV (eV.symm v)
        congr 1; apply eV.injective
        rw [Equiv.apply_symm_apply, ← hDb (eE.symm e), Equiv.apply_symm_apply]; exact he.2.1
      · have h := congrArg (fun t => (eE'.symm t).1) he.2.2
        simpa using h
    · intro e₁ _ e₂ _ h; exact hιinj h
    · intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨-, hb1, hb2⟩ := hb
      have hbt := hlift b (eE'.symm e') hb2
      refine ⟨eE ⟨cD.symm b, hbt⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · have h2 : cV (Quotient.mk (orbitRel (↥X) W) (cD.symm b).out.snd) = cV (eV.symm v) := by
            rw [← hbXc (cD.symm b), Equiv.apply_symm_apply]; exact hb1
          rw [hDb, cV.injective h2, Equiv.apply_symm_apply]
        · apply eE'.symm.injective; apply Subtype.ext
          rw [Equiv.symm_apply_apply]
          show μ₀.mapE (cD (eE.symm (eE ⟨cD.symm b, hbt⟩)).1) = (eE'.symm e').1
          rw [Equiv.symm_apply_apply]
          show μ₀.mapE (cD (cD.symm b)) = _
          rw [Equiv.apply_symm_apply]; exact hb2
      · show cD (eE.symm (eE ⟨cD.symm b, hbt⟩)).1 = b
        rw [Equiv.symm_apply_apply]; exact cD.apply_symm_apply b
    · intro e _; rfl
  ·
    intro v'
    rw [← μ₀.sum_degV (eV'.symm v')]
    refine Finset.sum_bij (fun v _ => κ v) ?_ ?_ ?_ ?_
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h := congrArg eV'.symm hv.2
      simpa using h
    · intro v₁ _ v₂ _ h; exact hκinj h
    · intro b hb
      rw [Finset.mem_filter] at hb
      refine ⟨eV (cV.symm b), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        show eV' (μ₀.mapV (cV (eV.symm (eV (cV.symm b))))) = v'
        rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply, hb.2, Equiv.apply_symm_apply]
      · show cV (eV.symm (eV (cV.symm b))) = b
        rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · intro v _; rfl
  ·
    intro v
    show eV' (μ₀.mapV (cV (eV.symm (eV (Quotient.mk (orbitRel (↥X) W) v))))) = _
    rw [Equiv.symm_apply_apply, hMV, houtXV]
  ·
    intro e
    show (eE'.symm (eE' ⟨μ₀.mapE (cD (eE.symm (eE e)).1), horE (eE.symm (eE e))⟩)).1 = _
    rw [Equiv.symm_apply_apply]
    show μ₀.mapE (cD (eE.symm (eE e)).1) = _
    rw [Equiv.symm_apply_apply]
    exact hME e.1
  ·
    show (μ₀.degTotal : ℕ) = _
    rw [hμtot]; rfl

#print axioms solution

end S_CerednikDrinfeld_Mumford_exists_finiteHom_orientedQuotient_of_conj_le
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_orientedQuotient_of_conj_le (solution)
