-- Prove2me | solution 1 for BUP.thm2_parity
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:24:17.572579+00:00
-- url     : https://prove2.me/submissions/231e4450-b578-4c00-b2b8-2f90379f9fca

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor
open BUP

universe g74o_u g74o_v g74o_w g74o_x g74o_y

theorem g74o_noBUP_false {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (C : InvSES A B) (D : BraidData A P Bg) (h : A →* A)
    (hb : ∃ b : B, b * b = 1 ∧ C.proj b ≠ 1)
    (hg : ∀ g : Bg, g * g = 1 → D.piBr g = 1) : ¬ NoBUP C D h := by
  rintro ⟨phi, psi, -, -, e3⟩
  obtain ⟨b, hb1, hb2⟩ := hb
  apply hb2
  rw [← e3]
  apply hg
  rw [← map_mul, hb1, map_one]

/-- parity of an integer, multiplicatively -/
def g74o_par : Multiplicative ℤ →* Z2 := (Int.castAddHom (ZMod 2)).toMultiplicative

theorem g74o_par_iff (u : Multiplicative ℤ) : g74o_par u = 1 ↔ ∃ t : Multiplicative ℤ, t ^ 2 = u := by
  constructor
  · intro h
    have h' : ((Multiplicative.toAdd u : ℤ) : ZMod 2) = 0 := congrArg Multiplicative.toAdd h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    obtain ⟨k, hk⟩ := h'
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, hk]
  · rintro ⟨t, rfl⟩
    apply Multiplicative.toAdd.injective
    show ((Multiplicative.toAdd (t ^ 2) : ℤ) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, toAdd_pow]
    exact ⟨Multiplicative.toAdd t, by simp⟩

theorem g74o_par_surj (z : Z2) : ∃ u : Multiplicative ℤ, g74o_par u = z := by
  have : ∀ z : Z2, z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
  rcases this z with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨Multiplicative.ofAdd 1, rfl⟩

theorem g74o_sq_inj (x y : Multiplicative ℤ) (h : x ^ 2 = y ^ 2) : x = y := by
  have := congrArg Multiplicative.toAdd h
  simp only [toAdd_pow, nsmul_eq_mul, Nat.cast_ofNat] at this
  apply Multiplicative.toAdd.injective
  omega

theorem g74o_sq_one (x : Multiplicative ℤ) (h : x * x = 1) : x = 1 := by
  have := congrArg Multiplicative.toAdd h
  simp only [toAdd_mul, toAdd_one] at this
  apply Multiplicative.toAdd.injective
  simp only [toAdd_one]; omega

/-- trivial involution extension A -> A x Z2 -> Z2 -/
def g74o_C0 (A : Type) [Group A] : InvSES A (A × Z2) where
  inj := MonoidHom.inl A Z2
  proj := MonoidHom.snd A Z2
  inj_inj x y h := congrArg Prod.fst h
  proj_surj z := ⟨(1, z), rfl⟩
  ex b := by
    constructor
    · intro h; exact ⟨b.1, Prod.ext rfl h.symm⟩
    · rintro ⟨a, rfl⟩; rfl

/-- torsion-free braid data: P = Bg = Z x A, iota squares the first factor -/
def g74o_D0 (A : Type) [CommGroup A] : BraidData A (Multiplicative ℤ × A) (Multiplicative ℤ × A) where
  iota := MonoidHom.prodMap (powMonoidHom 2) (MonoidHom.id A)
  piBr := g74o_par.comp (MonoidHom.fst _ _)
  p1 := MonoidHom.snd _ _
  iota_inj x y h := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (g74o_sq_inj _ _ h1) h2
  piBr_surj z := let ⟨u, hu⟩ := g74o_par_surj z; ⟨(u, 1), hu⟩
  ex g := by
    show g74o_par g.1 = 1 ↔ _
    rw [g74o_par_iff]
    constructor
    · rintro ⟨t, ht⟩; exact ⟨(t, g.2), Prod.ext ht rfl⟩
    · rintro ⟨p, rfl⟩; exact ⟨p.1, rfl⟩
  p1_surj a := ⟨(1, a), rfl⟩
  sigma := (Multiplicative.ofAdd 1, 1)
  sigma_ne := by
    show g74o_par (Multiplicative.ofAdd 1) ≠ 1
    decide
  lsigma := MulEquiv.refl _
  lsigma_conj p := by
    show _ = _ * _ * _
    rw [mul_comm (Multiplicative.ofAdd (1:ℤ), (1:A)), mul_inv_cancel_right]; rfl
  sigmaSq := (Multiplicative.ofAdd 1, 1)
  sigmaSq_eq := by ext <;> simp [pow_two]
  sigmaSq_triv := rfl

theorem g74o_D0_tf (A : Type) [CommGroup A] (g : Multiplicative ℤ × A) (hg : g * g = 1) :
    (g74o_D0 A).piBr g = 1 := by
  have : g.1 = 1 := g74o_sq_one _ (congrArg Prod.fst hg)
  show g74o_par g.1 = 1
  rw [this, map_one]

theorem g74o_Z2_sq (z : Z2) : z * z = 1 := by revert z; decide

/-- lifting to arbitrary universes -/
def g74o_up (G : Type) [Group G] : G →* ULift.{g74o_u} G :=
  (MulEquiv.ulift : ULift.{g74o_u} G ≃* G).symm.toMonoidHom
def g74o_dn (G : Type) [Group G] : ULift.{g74o_u} G →* G :=
  (MulEquiv.ulift : ULift.{g74o_u} G ≃* G).toMonoidHom
def g74o_ueq (G : Type) [Group G] : ULift.{g74o_u} G ≃* G := MulEquiv.ulift

def g74o_liftSES {A B : Type} [Group A] [Group B] (C : InvSES A B) :
    InvSES (ULift.{g74o_u} A) (ULift.{g74o_v} B) where
  inj := (g74o_up B).comp (C.inj.comp (g74o_dn A))
  proj := C.proj.comp (g74o_dn B)
  inj_inj x y h := ULift.ext _ _ (C.inj_inj _ _ (congrArg ULift.down h))
  proj_surj z := let ⟨b, hb⟩ := C.proj_surj z; ⟨ULift.up b, hb⟩
  ex b := by
    have := C.ex b.down
    constructor
    · intro h
      obtain ⟨a, ha⟩ := this.1 h
      exact ⟨ULift.up a, ULift.ext _ _ ha⟩
    · rintro ⟨a, ha⟩
      exact this.2 ⟨a.down, congrArg ULift.down ha⟩

def g74o_liftBD {A P Bg : Type} [Group A] [Group P] [Group Bg] (D : BraidData A P Bg) :
    BraidData (ULift.{g74o_u} A) (ULift.{g74o_v} P) (ULift.{g74o_w} Bg) where
  iota := (g74o_up Bg).comp (D.iota.comp (g74o_dn P))
  piBr := D.piBr.comp (g74o_dn Bg)
  p1 := (g74o_up A).comp (D.p1.comp (g74o_dn P))
  iota_inj x y h := ULift.ext _ _ (D.iota_inj _ _ (congrArg ULift.down h))
  piBr_surj z := let ⟨g, hg⟩ := D.piBr_surj z; ⟨ULift.up g, hg⟩
  ex g := by
    have := D.ex g.down
    constructor
    · intro h
      obtain ⟨a, ha⟩ := this.1 h
      exact ⟨ULift.up a, ULift.ext _ _ ha⟩
    · rintro ⟨a, ha⟩
      exact this.2 ⟨a.down, congrArg ULift.down ha⟩
  p1_surj a := let ⟨p, hp⟩ := D.p1_surj a.down; ⟨ULift.up p, ULift.ext _ _ hp⟩
  sigma := ULift.up D.sigma
  sigma_ne := D.sigma_ne
  lsigma := (g74o_ueq P).trans (D.lsigma.trans (g74o_ueq P).symm)
  lsigma_conj p := ULift.ext _ _ (D.lsigma_conj p.down)
  sigmaSq := ULift.up D.sigmaSq
  sigmaSq_eq := ULift.ext _ _ D.sigmaSq_eq
  sigmaSq_triv := ULift.ext _ _ D.sigmaSq_triv

theorem g74o_lift_false {A B P Bg : Type} [Group A] [Group B] [Group P] [Group Bg]
    (C : InvSES A B) (D : BraidData A P Bg)
    (hb : ∃ b : B, b * b = 1 ∧ C.proj b ≠ 1)
    (hg : ∀ g : Bg, g * g = 1 → D.piBr g = 1) (h : ULift.{g74o_u} A →* ULift.{g74o_u} A) :
    ¬ NoBUP (g74o_liftSES.{g74o_u, g74o_v} C) (g74o_liftBD.{g74o_u, g74o_w, g74o_x} D) h := by
  apply g74o_noBUP_false
  · obtain ⟨b, h1, h2⟩ := hb
    exact ⟨ULift.up b, ULift.ext _ _ h1, h2⟩
  · intro g hgg
    exact hg g.down (congrArg ULift.down hgg)

/-- the deck element of A x Z2 -/
theorem g74o_C0_deck (A : Type) [Group A] :
    ∃ b : A × Z2, b * b = 1 ∧ (g74o_C0 A).proj b ≠ 1 :=
  ⟨(1, Multiplicative.ofAdd 1), Prod.ext (mul_one _) (g74o_Z2_sq _),
    show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide⟩

theorem g74o_Z2_cases (z : Z2) : z = 1 ∨ z = Multiplicative.ofAdd 1 := by revert z; decide

theorem g74o_C0_act (A : Type) [Group A] (a : A) :
    ((1 : A), Multiplicative.ofAdd (1 : ZMod 2)) * (g74o_C0 A).inj a *
      ((1 : A), Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = (g74o_C0 A).inj a := by
  ext
  · simp [g74o_C0]
  · simp [g74o_C0]

theorem g74o_C0_gen (A : Type) [Group A] (b : A × Z2) :
    ∃ (a : A) (k : Int), b = (g74o_C0 A).inj a * ((1 : A), Multiplicative.ofAdd (1 : ZMod 2)) ^ k := by
  obtain ⟨a, z⟩ := b
  rcases g74o_Z2_cases z with rfl | rfl
  · exact ⟨a, 0, by ext <;> simp [g74o_C0]⟩
  · exact ⟨a, 1, by ext <;> simp [g74o_C0]⟩

def g74o_liftTW {A B P Bg : Type} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) :
    TorusWorld (ULift.{g74o_u} A) (ULift.{g74o_v} B) (ULift.{g74o_w} P) (ULift.{g74o_x} Bg) where
  C := g74o_liftSES.{g74o_u, g74o_v} W.C
  D := g74o_liftBD.{g74o_u, g74o_w, g74o_x} W.D
  coord := (g74o_ueq A).trans W.coord
  act := (g74o_ueq A).trans (W.act.trans (g74o_ueq A).symm)
  deckElem := ULift.up W.deckElem
  deckElem_ne := W.deckElem_ne
  deck_act a := ULift.ext _ _ (W.deck_act a.down)
  deckSq := ULift.up W.deckSq
  deckSq_eq := ULift.ext _ _ W.deckSq_eq
  gen b := by
    obtain ⟨a, k, h⟩ := W.gen b.down
    exact ⟨ULift.up a, k, ULift.ext _ _ (by show b.down = W.C.inj a * W.deckElem ^ k; exact h)⟩

def g74o_liftKW {A B P Bg T : Type} [Group A] [Group B] [Group P] [Group Bg] [Group T]
    (W : KleinWorld A B P Bg T) :
    KleinWorld (ULift.{g74o_u} A) (ULift.{g74o_v} B) (ULift.{g74o_w} P) (ULift.{g74o_x} Bg)
      (ULift.{g74o_y} T) where
  C := g74o_liftSES.{g74o_u, g74o_v} W.C
  D := g74o_liftBD.{g74o_u, g74o_w, g74o_x} W.D
  act := (g74o_ueq A).trans (W.act.trans (g74o_ueq A).symm)
  deckElem := ULift.up W.deckElem
  deckElem_ne := W.deckElem_ne
  deck_act a := ULift.ext _ _ (W.deck_act a.down)
  gen b := by
    obtain ⟨a, k, h⟩ := W.gen b.down
    exact ⟨ULift.up a, k, ULift.ext _ _ (by show b.down = W.C.inj a * W.deckElem ^ k; exact h)⟩
  torInj := (g74o_up A).comp (W.torInj.comp (g74o_dn T))
  torPar := W.torPar.comp (g74o_dn A)
  torInj_inj x y h := ULift.ext _ _ (W.torInj_inj _ _ (congrArg ULift.down h))
  torPar_surj z := by
    obtain ⟨a, ha⟩ := W.torPar_surj z
    exact ⟨ULift.up a, ha⟩
  tor_ex a := by
    have := W.tor_ex a.down
    constructor
    · intro h
      obtain ⟨t, ht⟩ := this.1 h
      exact ⟨ULift.up t, ULift.ext _ _ ht⟩
    · rintro ⟨t, ht⟩
      exact this.2 ⟨t.down, congrArg ULift.down ht⟩

abbrev g74o_T := Multiplicative (ℤ × ℤ)

/-- orientation-preserving model with order-two deck element and torsion-free braid group -/
def g74o_W0 : TorusWorld g74o_T (g74o_T × Z2) (Multiplicative ℤ × g74o_T)
    (Multiplicative ℤ × g74o_T) where
  C := g74o_C0 g74o_T
  D := g74o_D0 g74o_T
  coord := MulEquiv.refl _
  act := MulEquiv.refl _
  deckElem := (1, Multiplicative.ofAdd 1)
  deckElem_ne := show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide
  deck_act a := g74o_C0_act g74o_T a
  deckSq := 1
  deckSq_eq := by
    refine Prod.ext ?_ ?_
    · simp [g74o_C0]
    · exact (g74o_Z2_sq _).symm
  gen b := g74o_C0_gen g74o_T b

/-- Klein bottle model -/
def g74o_K0 : KleinWorld (Multiplicative ℤ) (Multiplicative ℤ × Z2)
    (Multiplicative ℤ × Multiplicative ℤ) (Multiplicative ℤ × Multiplicative ℤ)
    (Multiplicative ℤ) where
  C := g74o_C0 _
  D := g74o_D0 _
  act := MulEquiv.refl _
  deckElem := (1, Multiplicative.ofAdd 1)
  deckElem_ne := show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide
  deck_act a := g74o_C0_act _ a
  gen b := g74o_C0_gen _ b
  torInj := powMonoidHom 2
  torPar := g74o_par
  torInj_inj := g74o_sq_inj
  torPar_surj := g74o_par_surj
  tor_ex a := g74o_par_iff a

/-- dihedral parity -/
def g74o_par2 : DihedralGroup 0 →* Z2 where
  toFun
    | .r _ => 1
    | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (a | a) (b | b) <;>
      simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;> decide

def g74o_inj1 : g74o_T →* Multiplicative ℤ × DihedralGroup 0 where
  toFun a := (Multiplicative.ofAdd (Multiplicative.toAdd a).1, DihedralGroup.r (Multiplicative.toAdd a).2)
  map_one' := rfl
  map_mul' _ _ := rfl

def g74o_C1 : InvSES g74o_T (Multiplicative ℤ × DihedralGroup 0) where
  inj := g74o_inj1
  proj := g74o_par2.comp (MonoidHom.snd _ _)
  inj_inj x y h := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd _ at h1
    change DihedralGroup.r _ = DihedralGroup.r _ at h2
    injection h2 with h2
    apply Multiplicative.toAdd.injective
    exact Prod.ext (Multiplicative.ofAdd.injective h1) h2
  proj_surj z := by
    rcases g74o_Z2_cases z with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨(1, DihedralGroup.sr 0), rfl⟩
  ex b := by
    obtain ⟨k, d⟩ := b
    cases d with
    | r i =>
      exact ⟨fun _ => ⟨Multiplicative.ofAdd (Multiplicative.toAdd k, i), rfl⟩, fun _ => rfl⟩
    | sr i =>
      constructor
      · intro h
        exact absurd h (show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide)
      · rintro ⟨a, ha⟩
        have := congrArg Prod.snd ha
        simp [g74o_inj1] at this

def g74o_flip : g74o_T ≃* g74o_T :=
  AddEquiv.toMultiplicative (AddEquiv.prodCongr (AddEquiv.refl ℤ) (AddEquiv.neg ℤ))

theorem g74o_dh1 (x : ZMod 0) : (DihedralGroup.sr 0 : DihedralGroup 0) * DihedralGroup.r x *
        (DihedralGroup.sr 0)⁻¹ = DihedralGroup.r (-x) := by
  rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
  congr 1; simp
theorem g74o_dh2 : (DihedralGroup.r 0 : DihedralGroup 0) = DihedralGroup.sr 0 * DihedralGroup.sr 0 := by
  rw [DihedralGroup.sr_mul_sr]; simp
theorem g74o_dh3 (i : ZMod 0) : (DihedralGroup.sr i : DihedralGroup 0) = DihedralGroup.r (-i) * DihedralGroup.sr 0 := by
  rw [DihedralGroup.r_mul_sr]; simp

/-- orientation-reversing model -/
def g74o_W1 : TorusWorld g74o_T (Multiplicative ℤ × DihedralGroup 0) (Multiplicative ℤ × g74o_T)
    (Multiplicative ℤ × g74o_T) where
  C := g74o_C1
  D := g74o_D0 g74o_T
  coord := MulEquiv.refl _
  act := g74o_flip
  deckElem := (1, DihedralGroup.sr 0)
  deckElem_ne := show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide
  deck_act a := by
    ext
    · show 1 * Multiplicative.ofAdd (Multiplicative.toAdd a).1 * 1⁻¹ =
        Multiplicative.ofAdd (Multiplicative.toAdd a).1
      simp
    · show (DihedralGroup.sr 0 : DihedralGroup 0) * DihedralGroup.r (Multiplicative.toAdd a).2 *
        (DihedralGroup.sr 0)⁻¹ = DihedralGroup.r (-(Multiplicative.toAdd a).2)
      exact g74o_dh1 _
  deckSq := 1
  deckSq_eq := by
    ext
    · rfl
    · show (DihedralGroup.r 0 : DihedralGroup 0) = DihedralGroup.sr 0 * DihedralGroup.sr 0
      exact g74o_dh2
  gen b := by
    obtain ⟨k, d⟩ := b
    cases d with
    | r i =>
      refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd k, i), 0, ?_⟩
      simp only [zpow_zero, mul_one]
      rfl
    | sr i =>
      refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd k, -i), 1, ?_⟩
      simp only [zpow_one]
      ext
      · show k = Multiplicative.ofAdd (Multiplicative.toAdd k) * 1
        simp
      · show (DihedralGroup.sr i : DihedralGroup 0) = DihedralGroup.r (-i) * DihedralGroup.sr 0
        exact g74o_dh3 i

theorem g74o_W1_rev : TorusRev g74o_W1 := fun _ => ⟨rfl, rfl⟩

theorem g74o_C1_deck : ∃ b : Multiplicative ℤ × DihedralGroup 0, b * b = 1 ∧ g74o_C1.proj b ≠ 1 :=
  ⟨(1, DihedralGroup.sr 0), by ext <;> simp [DihedralGroup.sr_mul_sr],
    show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide⟩

theorem solution : ¬ (∀ {A B P Bg : Type} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (hr : TorusRev W) (h : A →* A),
    NoBUP W.C W.D h ↔
      ¬ ((W.beta11 h, W.beta21 h) ≠ ((0, 0) : Int × Int) ∧
        Even (W.beta12 h) ∧ Even (W.beta22 h))) := by
  intro H
  refine g74o_lift_false _ _ g74o_C1_deck (g74o_D0_tf _) 1
    ((H (g74o_liftTW g74o_W1) (fun a => g74o_W1_rev a.down) 1).2 ?_)
  rintro ⟨hne, -, -⟩
  apply hne
  simp [TorusWorld.beta11, TorusWorld.beta21, TorusWorld.coordsOf]
