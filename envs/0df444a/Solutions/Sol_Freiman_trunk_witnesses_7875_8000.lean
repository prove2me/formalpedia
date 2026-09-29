-- Prove2me | solution 1 for Freiman.trunk_witnesses_7875_8000
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T05:17:07.881167+00:00
-- url     : https://prove2.me/submissions/e09c9c50-f657-4b4f-9777-eedbdd4e5e69

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/- ===================================================================
   fastBound / fastBound?: if-chain lookup into the 4 literal
   trunkBoundData0{1,2,3,4} arrays, replacing the unoptimized
   `trunkBound C id = C.bounds[id-1]?.getD _` (which forces the kernel to
   re-walk the whole 4-way `trunkDataBounds` concatenation from scratch on
   every reference). See REPORT.md, technique (c).
   =================================================================== -/

def fastBound? (n : ℕ) : Option CertBound :=
  if n - 1 < 150 then trunkBoundData01[n-1]? else
  if n - 1 < 300 then trunkBoundData02[n-1-150]? else
  if n - 1 < 450 then trunkBoundData03[n-1-300]? else
  trunkBoundData04[n-1-450]?
def fastBound (n : ℕ) : CertBound := (fastBound? n).getD lowerHistoryZero

theorem hszB1 : trunkBoundData01.size = 150 := by decide +kernel
theorem hszB2 : trunkBoundData02.size = 150 := by decide +kernel
theorem hszB3 : trunkBoundData03.size = 150 := by decide +kernel
theorem hszB4 : trunkBoundData04.size = 102 := by decide +kernel
theorem cumB1 : trunkBoundData01.size = 150 := hszB1
theorem cumB2 : (trunkBoundData01 ++ trunkBoundData02).size = 300 := by
  rw [Array.size_append, cumB1, hszB2]
theorem cumB3 : (trunkBoundData01 ++ trunkBoundData02 ++ trunkBoundData03).size = 450 := by
  rw [Array.size_append, cumB2, hszB3]
theorem cumB4 : (trunkBoundData01 ++ trunkBoundData02 ++ trunkBoundData03 ++ trunkBoundData04).size = 552 := by
  rw [Array.size_append, cumB3, hszB4]

theorem bound_eq? (n : ℕ) : trunkDataBounds[n-1]? = fastBound? n := by
  unfold fastBound? trunkDataBounds
  rcases (show n - 1 < 150 ∨ (¬ n - 1 < 150 ∧ n - 1 < 300) ∨
      (¬ n - 1 < 150 ∧ ¬ n - 1 < 300 ∧ n - 1 < 450) ∨
      (¬ n - 1 < 150 ∧ ¬ n - 1 < 300 ∧ ¬ n - 1 < 450) by omega) with
    h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [if_pos h1,
      Array.getElem?_append_left (by rw [cumB3]; omega),
      Array.getElem?_append_left (by rw [cumB2]; omega),
      Array.getElem?_append_left (by rw [cumB1]; omega)]
  · rw [if_neg h1, if_pos h2,
      Array.getElem?_append_left (by rw [cumB3]; omega),
      Array.getElem?_append_left (by rw [cumB2]; omega),
      Array.getElem?_append_right (by rw [cumB1]; omega),
      show n - 1 - trunkBoundData01.size = n - 1 - 150 by rw [cumB1]]
  · rw [if_neg h1, if_neg h2, if_pos h3,
      Array.getElem?_append_left (by rw [cumB3]; omega),
      Array.getElem?_append_right (by rw [cumB2]; omega),
      show n - 1 - (trunkBoundData01 ++ trunkBoundData02).size = n - 1 - 300 by rw [cumB2]]
  · rw [if_neg h1, if_neg h2, if_neg h3,
      Array.getElem?_append_right (by rw [cumB3]; omega),
      show n - 1 - (trunkBoundData01 ++ trunkBoundData02 ++ trunkBoundData03).size = n - 1 - 450 by rw [cumB3]]

theorem bound_eq (n : ℕ) : trunkBound trunkCatalog n = fastBound n := by
  unfold trunkBound fastBound
  show trunkCatalog.bounds[n-1]?.getD lowerHistoryZero = _
  rw [show trunkCatalog.bounds = trunkDataBounds from rfl, bound_eq?]

theorem hboundfun : trunkBound trunkCatalog = fastBound := funext bound_eq

/- ===================================================================
   Boolean mirror of the diagonal=0 branch of `trunkWitnessValid`
   (explicit conjuncts, no `∀ i j : Fin 3`/Fintype machinery). See
   REPORT.md, technique (a).
   =================================================================== -/

def fcRect (R : CertRectangle) : Bool :=
  decide (R.r0 < R.r1) && decide (R.s0 < R.s1) && decide (0 ≤ R.r0)
def fcThr (t : CertThreshold) : Bool :=
  decide (0 ≤ certFieldLower t.x0) && decide (0 ≤ certFieldLower t.x1)
def fcCBV (z : CertField) (q : ℚ) : Bool :=
  decide (0 ≤ q) && (if q = 0 then decide (0 ≤ certFieldLower z) else decide (q < certFieldLower z))
def fcCBVs (C : CertPoly22) (m : ℚ) : Bool :=
  fcCBV (C 0 0) m && fcCBV (C 0 1) m && fcCBV (C 0 2) m &&
  fcCBV (C 1 0) m && fcCBV (C 1 1) m && fcCBV (C 1 2) m &&
  fcCBV (C 2 0) m && fcCBV (C 2 1) m && fcCBV (C 2 2) m

def fcRest0 (w : TrunkWitness) : Bool :=
  let l := fastBound w.lowerId
  let u := fastBound w.upperId
  decide (0 < w.lowerId) && decide (w.lowerId ≤ 552) && decide (0 < w.upperId) && decide (w.upperId ≤ 552) &&
  l.lower && !u.lower && fcRect w.rectangle && fcThr l.threshold && fcThr u.threshold &&
  (decide (0 < w.margin/2) || l.strict || u.strict)
def fcCoefBounds0 (w : TrunkWitness) : Bool :=
  let l := fastBound w.lowerId
  let u := fastBound w.upperId
  fcCBVs (certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) w.rectangle) (w.margin/2)

theorem fcRect_imp {R : CertRectangle} (h : fcRect R = true) :
    certRectangleValid R ∧ 0 ≤ R.r0 := by
  unfold fcRect at h; unfold certRectangleValid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩

theorem fcThr_imp {t : CertThreshold} (h : fcThr t = true) : certThresholdDataValid t := by
  unfold fcThr at h; unfold certThresholdDataValid
  simpa using h

theorem fcCBV_imp {z : CertField} {q : ℚ} (h : fcCBV z q = true) : certCoefficientBoundValid z q := by
  unfold fcCBV at h
  unfold certCoefficientBoundValid
  by_cases hq : q = 0 <;> simp_all

theorem fcCBVs_imp {C : CertPoly22} {m : ℚ} (h : fcCBVs C m = true) :
    ∀ i j : Fin 3, certCoefficientBoundValid (C i j) m := by
  unfold fcCBVs at h
  simp only [Bool.and_eq_true] at h
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact fcCBV_imp h.1.1.1.1.1.1.1.1
    | exact fcCBV_imp h.1.1.1.1.1.1.1.2
    | exact fcCBV_imp h.1.1.1.1.1.1.2
    | exact fcCBV_imp h.1.1.1.1.1.2
    | exact fcCBV_imp h.1.1.1.1.2
    | exact fcCBV_imp h.1.1.1.2
    | exact fcCBV_imp h.1.1.2
    | exact fcCBV_imp h.1.2
    | exact fcCBV_imp h.2

theorem fcRest0_imp {w : TrunkWitness} (h : fcRest0 w = true) :
    0 < w.lowerId ∧ w.lowerId ≤ 552 ∧ 0 < w.upperId ∧ w.upperId ≤ 552 ∧
    (fastBound w.lowerId).lower = true ∧ (fastBound w.upperId).lower = false ∧
    certRectangleValid w.rectangle ∧ 0 ≤ w.rectangle.r0 ∧
    certThresholdDataValid (fastBound w.lowerId).threshold ∧
    certThresholdDataValid (fastBound w.upperId).threshold ∧
    ((0 < w.margin/2 ∨ (fastBound w.lowerId).strict = true) ∨ (fastBound w.upperId).strict = true) := by
  unfold fcRest0 at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6, (fcRect_imp h7).1, (fcRect_imp h7).2, fcThr_imp h8, fcThr_imp h9, h10⟩

theorem fc0_imp {w : TrunkWitness} (hd : w.diagonal = 0)
    (h1 : fcRest0 w = true) (h2 : fcCoefBounds0 w = true) :
    trunkWitnessValid trunkCatalog w := by
  obtain ⟨e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11⟩ := fcRest0_imp h1
  unfold trunkWitnessValid
  rw [if_pos hd]
  refine ⟨e1,e2,e3,e4, ?_⟩
  unfold certWitnessValid trunkPairWitness trunkPolynomial
  rw [hboundfun]
  refine ⟨e5,e6,e7,e8,e9,e10, rfl, fcCBVs_imp h2, ?_⟩
  rcases e11 with (e11 | e11) | e11
  · exact Or.inl (fun _ _ => e11)
  · exact Or.inr (Or.inl e11)
  · exact Or.inr (Or.inr e11)

theorem chunk_mem {s n j : ℕ} (h1 : s ≤ j) (h2 : j < s + n) : j ∈ List.range' s n :=
  List.mem_range'_1.mpr ⟨h1, h2⟩

def dflt : TrunkWitness := ⟨0,0,⟨0,1,0,1⟩,0,0⟩

/- trunk_witnesses_7875_8000 : trunkWitnessBatch 7875 8000 (sub-array trunkWitnessData32, local range [125,250), EXCLUDES diagonal!=0 indices (237, 238)) -/

/- Part: sizes of the 35 literal witness sub-arrays. -/
theorem hsz01 : trunkWitnessData01.size = 250 := by decide +kernel
theorem hsz02 : trunkWitnessData02.size = 250 := by decide +kernel
theorem hsz03 : trunkWitnessData03.size = 250 := by decide +kernel
theorem hsz04 : trunkWitnessData04.size = 250 := by decide +kernel
theorem hsz05 : trunkWitnessData05.size = 250 := by decide +kernel
theorem hsz06 : trunkWitnessData06.size = 250 := by decide +kernel
theorem hsz07 : trunkWitnessData07.size = 250 := by decide +kernel
theorem hsz08 : trunkWitnessData08.size = 250 := by decide +kernel
theorem hsz09 : trunkWitnessData09.size = 250 := by decide +kernel
theorem hsz10 : trunkWitnessData10.size = 250 := by decide +kernel
theorem hsz11 : trunkWitnessData11.size = 250 := by decide +kernel
theorem hsz12 : trunkWitnessData12.size = 250 := by decide +kernel
theorem hsz13 : trunkWitnessData13.size = 250 := by decide +kernel
theorem hsz14 : trunkWitnessData14.size = 250 := by decide +kernel
theorem hsz15 : trunkWitnessData15.size = 250 := by decide +kernel
theorem hsz16 : trunkWitnessData16.size = 250 := by decide +kernel
theorem hsz17 : trunkWitnessData17.size = 250 := by decide +kernel
theorem hsz18 : trunkWitnessData18.size = 250 := by decide +kernel
theorem hsz19 : trunkWitnessData19.size = 250 := by decide +kernel
theorem hsz20 : trunkWitnessData20.size = 250 := by decide +kernel
theorem hsz21 : trunkWitnessData21.size = 250 := by decide +kernel
theorem hsz22 : trunkWitnessData22.size = 250 := by decide +kernel
theorem hsz23 : trunkWitnessData23.size = 250 := by decide +kernel
theorem hsz24 : trunkWitnessData24.size = 250 := by decide +kernel
theorem hsz25 : trunkWitnessData25.size = 250 := by decide +kernel
theorem hsz26 : trunkWitnessData26.size = 250 := by decide +kernel
theorem hsz27 : trunkWitnessData27.size = 250 := by decide +kernel
theorem hsz28 : trunkWitnessData28.size = 250 := by decide +kernel
theorem hsz29 : trunkWitnessData29.size = 250 := by decide +kernel
theorem hsz30 : trunkWitnessData30.size = 250 := by decide +kernel
theorem hsz31 : trunkWitnessData31.size = 250 := by decide +kernel
theorem hsz32 : trunkWitnessData32.size = 250 := by decide +kernel
theorem hsz33 : trunkWitnessData33.size = 250 := by decide +kernel
theorem hsz34 : trunkWitnessData34.size = 250 := by decide +kernel
theorem hsz35 : trunkWitnessData35.size = 156 := by decide +kernel

/- Part: cumulative-size chain (never touches array contents). -/
theorem cum01 : trunkWitnessData01.size = 250 := hsz01
theorem cum02 : (trunkWitnessData01++trunkWitnessData02).size = 500 := by rw [Array.size_append, cum01, hsz02]
theorem cum03 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03).size = 750 := by rw [Array.size_append, cum02, hsz03]
theorem cum04 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04).size = 1000 := by rw [Array.size_append, cum03, hsz04]
theorem cum05 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05).size = 1250 := by rw [Array.size_append, cum04, hsz05]
theorem cum06 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06).size = 1500 := by rw [Array.size_append, cum05, hsz06]
theorem cum07 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07).size = 1750 := by rw [Array.size_append, cum06, hsz07]
theorem cum08 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08).size = 2000 := by rw [Array.size_append, cum07, hsz08]
theorem cum09 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09).size = 2250 := by rw [Array.size_append, cum08, hsz09]
theorem cum10 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10).size = 2500 := by rw [Array.size_append, cum09, hsz10]
theorem cum11 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11).size = 2750 := by rw [Array.size_append, cum10, hsz11]
theorem cum12 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12).size = 3000 := by rw [Array.size_append, cum11, hsz12]
theorem cum13 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13).size = 3250 := by rw [Array.size_append, cum12, hsz13]
theorem cum14 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14).size = 3500 := by rw [Array.size_append, cum13, hsz14]
theorem cum15 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15).size = 3750 := by rw [Array.size_append, cum14, hsz15]
theorem cum16 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16).size = 4000 := by rw [Array.size_append, cum15, hsz16]
theorem cum17 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17).size = 4250 := by rw [Array.size_append, cum16, hsz17]
theorem cum18 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18).size = 4500 := by rw [Array.size_append, cum17, hsz18]
theorem cum19 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19).size = 4750 := by rw [Array.size_append, cum18, hsz19]
theorem cum20 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20).size = 5000 := by rw [Array.size_append, cum19, hsz20]
theorem cum21 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21).size = 5250 := by rw [Array.size_append, cum20, hsz21]
theorem cum22 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22).size = 5500 := by rw [Array.size_append, cum21, hsz22]
theorem cum23 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23).size = 5750 := by rw [Array.size_append, cum22, hsz23]
theorem cum24 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24).size = 6000 := by rw [Array.size_append, cum23, hsz24]
theorem cum25 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25).size = 6250 := by rw [Array.size_append, cum24, hsz25]
theorem cum26 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26).size = 6500 := by rw [Array.size_append, cum25, hsz26]
theorem cum27 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27).size = 6750 := by rw [Array.size_append, cum26, hsz27]
theorem cum28 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28).size = 7000 := by rw [Array.size_append, cum27, hsz28]
theorem cum29 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29).size = 7250 := by rw [Array.size_append, cum28, hsz29]
theorem cum30 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30).size = 7500 := by rw [Array.size_append, cum29, hsz30]
theorem cum31 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31).size = 7750 := by rw [Array.size_append, cum30, hsz31]
theorem cum32 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32).size = 8000 := by rw [Array.size_append, cum31, hsz32]
theorem cum33 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33).size = 8250 := by rw [Array.size_append, cum32, hsz33]
theorem cum34 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33++trunkWitnessData34).size = 8500 := by rw [Array.size_append, cum33, hsz34]
theorem cum35 : (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33++trunkWitnessData34++trunkWitnessData35).size = 8656 := by rw [Array.size_append, cum34, hsz35]

/- Part: locate this leaf's witnesses in sub-array trunkWitnessData32 by directed peel. -/
theorem hidx (i : ℕ) (hib : i < 250) :
    (trunkDataWitnesses[i + 7750]?).getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩ = (trunkWitnessData32[i]?).getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩ := by
  unfold trunkDataWitnesses
  rw [Array.getElem?_append_left (show i + 7750 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33++trunkWitnessData34).size by rw [cum34]; omega)]
  rw [Array.getElem?_append_left (show i + 7750 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32++trunkWitnessData33).size by rw [cum33]; omega)]
  rw [Array.getElem?_append_left (show i + 7750 < (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31++trunkWitnessData32).size by rw [cum32]; omega)]
  rw [Array.getElem?_append_right (show (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31).size ≤ i + 7750 by rw [cum31]; omega)]
  rw [show i + 7750 - (trunkWitnessData01++trunkWitnessData02++trunkWitnessData03++trunkWitnessData04++trunkWitnessData05++trunkWitnessData06++trunkWitnessData07++trunkWitnessData08++trunkWitnessData09++trunkWitnessData10++trunkWitnessData11++trunkWitnessData12++trunkWitnessData13++trunkWitnessData14++trunkWitnessData15++trunkWitnessData16++trunkWitnessData17++trunkWitnessData18++trunkWitnessData19++trunkWitnessData20++trunkWitnessData21++trunkWitnessData22++trunkWitnessData23++trunkWitnessData24++trunkWitnessData25++trunkWitnessData26++trunkWitnessData27++trunkWitnessData28++trunkWitnessData29++trunkWitnessData30++trunkWitnessData31).size = i by rw [cum31]; omega]

/- Part: certificate checks for the diag=0 witnesses, 3 chunk(s). -/
theorem batchRest0 : ∀ j ∈ List.range' 125 56,
    fcRest0 (trunkWitnessData32[j]?.getD dflt) = true := by decide +kernel
theorem batchCoef0 : ∀ j ∈ List.range' 125 56,
    fcCoefBounds0 (trunkWitnessData32[j]?.getD dflt) = true := by decide +kernel
theorem batchDiag0 : ∀ j ∈ List.range' 125 56,
    (trunkWitnessData32[j]?.getD dflt).diagonal = 0 := by decide +kernel
theorem batchRest1 : ∀ j ∈ List.range' 181 56,
    fcRest0 (trunkWitnessData32[j]?.getD dflt) = true := by decide +kernel
theorem batchCoef1 : ∀ j ∈ List.range' 181 56,
    fcCoefBounds0 (trunkWitnessData32[j]?.getD dflt) = true := by decide +kernel
theorem batchDiag1 : ∀ j ∈ List.range' 181 56,
    (trunkWitnessData32[j]?.getD dflt).diagonal = 0 := by decide +kernel
theorem batchRest2 : ∀ j ∈ List.range' 239 11,
    fcRest0 (trunkWitnessData32[j]?.getD dflt) = true := by decide +kernel
theorem batchCoef2 : ∀ j ∈ List.range' 239 11,
    fcCoefBounds0 (trunkWitnessData32[j]?.getD dflt) = true := by decide +kernel
theorem batchDiag2 : ∀ j ∈ List.range' 239 11,
    (trunkWitnessData32[j]?.getD dflt).diagonal = 0 := by decide +kernel

/- Part: the 2 diagonal!=0 witnesses, checked directly (single concrete witness -- no batching/mirror needed). -/
theorem specialA : trunkWitnessValid trunkCatalog (trunkWitnessData32[237]?.getD dflt) := by
  unfold trunkWitnessValid trunkPairWitness trunkPolynomial trunkDiagonalCoefficient
    trunkCorner certWitnessValid certRectangleValid certThresholdDataValid
    certCoefficientBoundValid
  rw [hboundfun]
  decide +kernel
theorem specialB : trunkWitnessValid trunkCatalog (trunkWitnessData32[238]?.getD dflt) := by
  unfold trunkWitnessValid trunkPairWitness trunkPolynomial trunkDiagonalCoefficient
    trunkCorner certWitnessValid certRectangleValid certThresholdDataValid
    certCoefficientBoundValid
  rw [hboundfun]
  decide +kernel

theorem key : ∀ j ∈ List.range' 125 125,
    trunkWitnessValid trunkCatalog (trunkWitnessData32[j]?.getD dflt) := by
  intro j hj
  simp only [List.mem_range'_1] at hj
  rcases (show (125 ≤ j ∧ j < 181) ∨ (181 ≤ j ∧ j < 237) ∨ (239 ≤ j ∧ j < 250) ∨ (j = 237 ∨ j = 238) by omega) with
    h0 | h1 | h2 | (rfl | rfl)
  · exact fc0_imp (batchDiag0 j (chunk_mem h0.1 h0.2)) (batchRest0 j (chunk_mem h0.1 h0.2)) (batchCoef0 j (chunk_mem h0.1 h0.2))
  · exact fc0_imp (batchDiag1 j (chunk_mem h1.1 h1.2)) (batchRest1 j (chunk_mem h1.1 h1.2)) (batchCoef1 j (chunk_mem h1.1 h1.2))
  · exact fc0_imp (batchDiag2 j (chunk_mem h2.1 h2.2)) (batchRest2 j (chunk_mem h2.1 h2.2)) (batchCoef2 j (chunk_mem h2.1 h2.2))
  · exact specialA
  · exact specialB

theorem solution : trunkWitnessBatch 7875 8000 := by
  intro i hlo hhi
  have heq : trunkWitness trunkCatalog (i+1) = trunkWitnessData32[i - 7750]?.getD dflt := by
    unfold trunkWitness
    simp only [Nat.add_sub_cancel]
    show trunkCatalog.witnesses[i]?.getD _ = _
    rw [show trunkCatalog.witnesses = trunkDataWitnesses from rfl]
    have := hidx (i - 7750) (show i - 7750 < 250 by omega)
    rwa [show i - 7750 + 7750 = i by omega] at this
  rw [heq]
  have hj : i - 7750 ∈ List.range' 125 125 := chunk_mem (by omega) (by omega)
  exact key (i - 7750) hj
